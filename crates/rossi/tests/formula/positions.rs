//! Subformula positions: numbering, navigation, lookup, replacement.

use rossi::formula::tag::{AssocPredOp, BinaryExprOp, QuantExprOp};
use rossi::formula::{
    Expression, ExpressionKind, Form, FormulaRef, Position, PositionError, PredicateKind, Type,
};

use crate::common::{bid, decl, decl_ty, eq_pred, ff, fid, fid_ty, forall, int};

fn pos(s: &str) -> Position {
    s.parse().expect("valid position")
}

fn as_expr<'a>(r: FormulaRef<'a>) -> &'a Expression {
    match r {
        FormulaRef::Expr(e) => e,
        _ => panic!("expected an expression"),
    }
}

// --- numbering ---

#[test]
fn quantified_predicates_number_declarations_then_body() {
    // ∀x,y · x = y
    let pred = forall(vec![decl("x"), decl("y")], eq_pred(bid(1), bid(0)));

    match pred.sub_formula(&pos("0")) {
        Some(FormulaRef::Decl(d)) => assert_eq!(d.name(), "x"),
        other => panic!("expected declaration, got {other:?}"),
    }
    match pred.sub_formula(&pos("1")) {
        Some(FormulaRef::Decl(d)) => assert_eq!(d.name(), "y"),
        other => panic!("expected declaration, got {other:?}"),
    }
    match pred.sub_formula(&pos("2")) {
        Some(FormulaRef::Pred(p)) => {
            assert!(matches!(p.kind(), PredicateKind::Relational { .. }));
        }
        other => panic!("expected body, got {other:?}"),
    }
    // Inside the body: 2.0 = left, 2.1 = right.
    assert!(matches!(
        as_expr(pred.sub_formula(&pos("2.0")).unwrap()).kind(),
        ExpressionKind::BoundIdentifier(1)
    ));
    assert!(matches!(
        as_expr(pred.sub_formula(&pos("2.1")).unwrap()).kind(),
        ExpressionKind::BoundIdentifier(0)
    ));
    assert!(pred.sub_formula(&pos("3")).is_none());
    assert!(pred.sub_formula(&pos("2.0.0")).is_none());
}

#[test]
fn quantified_expressions_add_the_value_expression_last() {
    // {x · x = 1 ∣ x}
    let cset = ff().quantified_expression(
        QuantExprOp::CSet,
        vec![decl("x")],
        eq_pred(bid(0), int(1)),
        bid(0),
        None,
        Form::Explicit,
    );
    assert!(matches!(
        cset.sub_formula(&pos("0")),
        Some(FormulaRef::Decl(_))
    ));
    assert!(matches!(
        cset.sub_formula(&pos("1")),
        Some(FormulaRef::Pred(_))
    ));
    assert!(matches!(
        cset.sub_formula(&pos("2")),
        Some(FormulaRef::Expr(_))
    ));
    assert!(cset.sub_formula(&pos("3")).is_none());
}

#[test]
fn root_position_is_the_formula_itself() {
    let pred = eq_pred(fid("x"), int(1));
    assert!(matches!(
        pred.sub_formula(&Position::root()),
        Some(FormulaRef::Pred(_))
    ));
}

// --- navigation and ordering ---

#[test]
fn navigation_walks_the_index_path() {
    let p = pos("1.0.2");
    assert_eq!(p.parent(), Some(pos("1.0")));
    assert_eq!(p.child(4), pos("1.0.2.4"));
    assert_eq!(p.next_sibling(), Some(pos("1.0.3")));
    assert_eq!(p.previous_sibling(), Some(pos("1.0.1")));
    assert_eq!(pos("1.0.0").previous_sibling(), None);
    assert_eq!(Position::root().parent(), None);
    assert_eq!(p.child_index(), Some(2));
    assert_eq!(p.to_string(), "1.0.2");
    assert_eq!(Position::root().to_string(), "");
}

#[test]
fn positions_come_out_in_pre_order() {
    let pred = forall(
        vec![decl("x")],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![eq_pred(bid(0), int(1)), eq_pred(fid("y"), int(2))],
            None,
        ),
    );
    let all = pred.positions(&mut |_| true);
    let mut sorted = all.clone();
    sorted.sort();
    assert_eq!(all, sorted);
    // Root first, then the declaration, then the conjunction and its
    // subtrees depth-first.
    assert_eq!(all.first(), Some(&Position::root()));
    assert_eq!(all[1], pos("0"));
    assert_eq!(all[2], pos("1"));
    assert_eq!(all[3], pos("1.0"));
}

#[test]
fn position_filters_select_nodes() {
    let pred = eq_pred(
        ff().binary_expression(BinaryExprOp::FunImage, fid("f"), fid("x"), None),
        int(1),
    );
    // All function applications.
    let hits = pred.positions(&mut |r| {
        matches!(
            r,
            FormulaRef::Expr(e) if matches!(
                e.kind(),
                ExpressionKind::Binary { op: BinaryExprOp::FunImage, .. }
            )
        )
    });
    assert_eq!(hits, [pos("0")]);
}

// --- replacement ---

#[test]
fn rewrite_replaces_the_addressed_subformula() {
    let pred = eq_pred(fid("x"), int(1));
    let replaced = pred
        .rewrite_sub_formula(&pos("1"), FormulaRef::Expr(&int(2)))
        .expect("replacement fits");
    assert_eq!(replaced, eq_pred(fid("x"), int(2)));
    // The original is untouched.
    assert_eq!(pred, eq_pred(fid("x"), int(1)));
}

#[test]
fn rewrite_round_trips_every_position() {
    let pred = forall(
        vec![decl_ty("x", Type::Int)],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![
                eq_pred(bid(0), int(1)),
                eq_pred(
                    ff().binary_expression(BinaryExprOp::FunImage, fid("f"), bid(0), None),
                    fid("y"),
                ),
            ],
            None,
        ),
    );
    for position in pred.positions(&mut |_| true) {
        let sub = pred.sub_formula(&position).expect("position exists");
        let rewritten = pred
            .rewrite_sub_formula(&position, sub)
            .expect("identical replacement fits");
        assert_eq!(rewritten, pred, "at {position}");
    }
}

#[test]
fn rewrite_rejects_class_and_type_mismatches() {
    let typed = eq_pred(fid_ty("x", Type::Int), int(1));

    // A predicate cannot replace an expression.
    let bool_pred = eq_pred(int(1), int(1));
    assert_eq!(
        typed.rewrite_sub_formula(&pos("0"), FormulaRef::Pred(&bool_pred)),
        Err(PositionError::IncompatibleReplacement)
    );

    // A typed subformula keeps its type.
    assert_eq!(
        typed.rewrite_sub_formula(&pos("0"), FormulaRef::Expr(&fid_ty("y", Type::Bool))),
        Err(PositionError::IncompatibleReplacement)
    );

    // An untyped replacement for a typed subformula is also rejected.
    assert_eq!(
        typed.rewrite_sub_formula(&pos("0"), FormulaRef::Expr(&fid("y"))),
        Err(PositionError::IncompatibleReplacement)
    );

    // Same type: accepted.
    assert!(
        typed
            .rewrite_sub_formula(&pos("0"), FormulaRef::Expr(&fid_ty("y", Type::Int)))
            .is_ok()
    );

    // Out of range.
    assert_eq!(
        typed.rewrite_sub_formula(&pos("5"), FormulaRef::Expr(&int(1))),
        Err(PositionError::OutOfRange)
    );
}

#[test]
fn rewrite_can_replace_a_declaration() {
    let pred = forall(vec![decl_ty("x", Type::Int)], eq_pred(bid(0), int(1)));
    let renamed = pred
        .rewrite_sub_formula(&pos("0"), FormulaRef::Decl(&decl_ty("fresh", Type::Int)))
        .expect("same-typed declaration fits");
    // Alpha-equivalent: the declaration name is a hint.
    assert_eq!(renamed, pred);

    // A declaration of another type is rejected.
    assert_eq!(
        pred.rewrite_sub_formula(&pos("0"), FormulaRef::Decl(&decl_ty("fresh", Type::Bool))),
        Err(PositionError::IncompatibleReplacement)
    );
}

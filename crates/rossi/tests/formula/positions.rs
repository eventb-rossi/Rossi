//! Subformula positions: numbering, navigation, lookup, replacement.

use rossi::formula::tag::{AssocPredOp, BinaryExprOp, BinaryPredOp, QuantExprOp};
use rossi::formula::{
    Expression, ExpressionKind, Form, FormulaRef, Position, PositionError, Predicate,
    PredicateKind, Type,
};

use crate::common::{bfalse, bid, btrue, decl, decl_ty, eq_pred, ff, fid, fid_ty, forall, int};

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

// --- propositional leaves ---

/// `∧` over `children`.
fn and(children: Vec<Predicate>) -> Predicate {
    ff().associative_predicate(AssocPredOp::LAnd, children, None)
}

/// `∨` over `children`.
fn or(children: Vec<Predicate>) -> Predicate {
    ff().associative_predicate(AssocPredOp::LOr, children, None)
}

/// `¬ child`.
fn not(child: Predicate) -> Predicate {
    ff().not_predicate(child, None)
}

/// `left ⇒ right`.
fn implies(left: Predicate, right: Predicate) -> Predicate {
    ff().binary_predicate(BinaryPredOp::LImp, left, right, None)
}

/// `left ⇔ right`.
fn equiv(left: Predicate, right: Predicate) -> Predicate {
    ff().binary_predicate(BinaryPredOp::LEqv, left, right, None)
}

/// A distinct atomic condition, `<name> = <value>`.
fn atom(name: &str, value: i64) -> Predicate {
    eq_pred(fid(name), int(value))
}

fn positions_of(specs: &[&str]) -> Vec<Position> {
    specs.iter().copied().map(pos).collect()
}

/// What a consumer numbering atomic conditions has to descend through.
/// Spelled here so the tests below state the rule once.
fn is_connective(p: &Predicate) -> bool {
    matches!(
        p.kind(),
        PredicateKind::Associative { .. } | PredicateKind::Binary { .. } | PredicateKind::Not(_)
    )
}

#[test]
fn a_predicate_without_connectives_is_its_own_leaf() {
    // Including ⊤ and ⊥, which carry no propositional structure of their own.
    assert_eq!(atom("x", 1).propositional_leaves(), [Position::root()]);
    assert_eq!(btrue().propositional_leaves(), [Position::root()]);
    assert_eq!(bfalse().propositional_leaves(), [Position::root()]);
}

#[test]
fn an_n_ary_conjunction_numbers_its_children_left_to_right() {
    // x = 1 ∧ y = 2 ∧ z = 3 — one flat node, not a right-leaning spine, so
    // the leaf order does not depend on how the source associated it.
    let pred = and(vec![atom("x", 1), atom("y", 2), atom("z", 3)]);
    assert_eq!(pred.propositional_leaves(), positions_of(&["0", "1", "2"]));
}

#[test]
fn nested_connectives_come_out_left_to_right() {
    // (x = 1 ∧ y = 2) ∨ ¬ z = 3
    let pred = or(vec![
        and(vec![atom("x", 1), atom("y", 2)]),
        not(atom("z", 3)),
    ]);
    assert_eq!(
        pred.propositional_leaves(),
        positions_of(&["0.0", "0.1", "1.0"])
    );

    // The ¬ itself is not a leaf; the atom under it is.
    match pred.sub_formula(&pos("1.0")) {
        Some(FormulaRef::Pred(p)) => {
            assert!(matches!(p.kind(), PredicateKind::Relational { .. }));
        }
        other => panic!("expected the negated atom, got {other:?}"),
    }
}

#[test]
fn implication_and_equivalence_are_connectives() {
    // (x = 1 ⇒ y = 2) ⇔ z = 3
    let pred = equiv(implies(atom("x", 1), atom("y", 2)), atom("z", 3));
    assert_eq!(
        pred.propositional_leaves(),
        positions_of(&["0.0", "0.1", "1"])
    );
}

#[test]
fn a_quantifier_is_a_leaf_and_its_body_is_not_entered() {
    // (∀x · x = 1) ∧ y = 2 — the quantifier is one atomic condition. Its
    // body is a conjunction-free predicate here only incidentally; what
    // matters is that the descent stops at the binder.
    let pred = and(vec![
        forall(vec![decl("x")], and(vec![atom("y", 1), atom("z", 2)])),
        atom("w", 3),
    ]);
    assert_eq!(pred.propositional_leaves(), positions_of(&["0", "1"]));

    // `positions` cannot express this: it descends past the binder and
    // returns the body's conjuncts too.
    let filtered = pred.positions(&mut |r| matches!(r, FormulaRef::Pred(p) if !is_connective(p)));
    assert_eq!(filtered, positions_of(&["0", "0.1.0", "0.1.1", "1"]));
}

#[test]
fn a_bool_expression_interior_is_not_entered() {
    // bool(x = 1 ∧ y = 2) = TRUE ∧ z = 3 — the relational is one leaf, even
    // though a conjunction hides inside its operand.
    let inner = and(vec![atom("x", 1), atom("y", 2)]);
    let relational = eq_pred(ff().bool_expression(inner, None), fid("TRUE"));
    let pred = and(vec![relational, atom("z", 3)]);

    assert_eq!(pred.propositional_leaves(), positions_of(&["0", "1"]));
}

#[test]
fn leaves_are_sorted_addressable_predicates_within_all_positions() {
    let pred = or(vec![
        implies(and(vec![atom("a", 1), not(atom("b", 2))]), atom("c", 3)),
        equiv(atom("d", 4), forall(vec![decl("x")], atom("e", 5))),
    ]);
    let leaves = pred.propositional_leaves();

    // Pre-order, like every other position listing.
    let mut sorted = leaves.clone();
    sorted.sort();
    assert_eq!(leaves, sorted);

    // A subset of the full listing.
    let all = pred.positions(&mut |_| true);
    assert!(leaves.iter().all(|position| all.contains(position)));

    // Every leaf addresses a predicate, and none is a connective.
    // Replacement round-tripping is covered for every position, leaves
    // included, by `rewrite_round_trips_every_position`.
    for position in &leaves {
        let FormulaRef::Pred(leaf) = pred.sub_formula(position).expect("position exists") else {
            panic!("expected a predicate at {position}");
        };
        assert!(
            !is_connective(leaf),
            "connective left in the leaves at {position}"
        );
    }
}

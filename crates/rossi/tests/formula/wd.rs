//! Well-definedness lemmas: the operator table and the constructive
//! simplifications.

use rossi::formula::tag::{
    AssocPredOp, AtomicOp, BinaryExprOp, BinaryPredOp, QuantExprOp, QuantPredOp, RelationalOp,
    UnaryExprOp,
};
use rossi::formula::{Expression, Form, Type, TypeEnvironmentBuilder};

use crate::common::{bid, btrue, checked, decl, env, eq_pred, ff, fid, forall, int};

/// A typed integer identifier.
fn iid(name: &str) -> Expression {
    ff().free_identifier(name, None, Some(Type::Int))
}

fn div(left: Expression, right: Expression) -> Expression {
    ff().binary_expression(BinaryExprOp::Div, left, right, None)
}

// --- total constructs ---

#[test]
fn total_formulas_have_trivial_lemmas() {
    let pred = checked(eq_pred(fid("x"), int(1)), &env(&[("x", Type::Int)]));
    assert_eq!(pred.wd_lemma_raw(), btrue());
}

#[test]
fn builtin_total_functions_have_trivial_application_lemmas() {
    // succ(5) = x
    let pred = checked(
        eq_pred(
            ff().binary_expression(
                BinaryExprOp::FunImage,
                ff().atomic_expression(AtomicOp::KSucc, None, None),
                int(5),
                None,
            ),
            fid("x"),
        ),
        &env(&[("x", Type::Int)]),
    );
    assert_eq!(pred.wd_lemma_raw(), btrue());
}

// --- arithmetic guards ---

#[test]
fn division_guards_the_divisor() {
    let pred = checked(
        eq_pred(div(iid("a"), iid("b")), int(1)),
        &env(&[("a", Type::Int), ("b", Type::Int)]),
    );
    // b ≠ 0
    let expected = ff().relational_predicate(RelationalOp::NotEqual, iid("b"), int(0), None);
    assert_eq!(pred.wd_lemma_raw(), expected);
}

#[test]
fn modulo_and_exponent_guard_their_operands() {
    let environment = env(&[("a", Type::Int), ("b", Type::Int)]);
    let modulo = checked(
        eq_pred(
            ff().binary_expression(BinaryExprOp::Mod, iid("a"), iid("b"), None),
            int(1),
        ),
        &environment,
    );
    // 0 ≤ a ∧ 0 < b
    let expected = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![
            ff().relational_predicate(RelationalOp::Le, int(0), iid("a"), None),
            ff().relational_predicate(RelationalOp::Lt, int(0), iid("b"), None),
        ],
        None,
    );
    assert_eq!(modulo.wd_lemma_raw(), expected);

    let expn = checked(
        eq_pred(
            ff().binary_expression(BinaryExprOp::Expn, iid("a"), iid("b"), None),
            int(1),
        ),
        &environment,
    );
    let expected = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![
            ff().relational_predicate(RelationalOp::Le, int(0), iid("a"), None),
            ff().relational_predicate(RelationalOp::Le, int(0), iid("b"), None),
        ],
        None,
    );
    assert_eq!(expn.wd_lemma_raw(), expected);
}

// --- function application ---

#[test]
fn function_application_guards_domain_and_functionality() {
    let f_ty = Type::relation(Type::given("S"), Type::Int);
    let mut builder = TypeEnvironmentBuilder::new();
    builder.add_given_set("S");
    builder.insert("f", f_ty.clone());
    builder.insert("e", Type::given("S"));
    let environment = builder.make_snapshot();

    let pred = checked(
        eq_pred(
            ff().binary_expression(BinaryExprOp::FunImage, fid("f"), fid("e"), None),
            int(1),
        ),
        &environment,
    );

    let f = ff().free_identifier("f", None, Some(f_ty));
    let e = ff().free_identifier("e", None, Some(Type::given("S")));
    let dom = ff().unary_expression(UnaryExprOp::KDom, f.clone(), None);
    let in_domain = ff().relational_predicate(RelationalOp::In, e, dom, None);
    let s_expr = Type::given("S").to_expression(&ff());
    let int_expr = Type::Int.to_expression(&ff());
    let pfun = ff().binary_expression(BinaryExprOp::PFun, s_expr, int_expr, None);
    let functional = ff().relational_predicate(RelationalOp::In, f, pfun, None);
    let expected = ff().associative_predicate(AssocPredOp::LAnd, vec![in_domain, functional], None);
    assert_eq!(pred.wd_lemma_raw(), expected);
}

// --- set operators ---

#[test]
fn cardinality_requires_finiteness() {
    let pred = checked(
        eq_pred(
            ff().unary_expression(UnaryExprOp::KCard, fid("s"), None),
            int(1),
        ),
        &env(&[("s", Type::pow(Type::Int))]),
    );
    let s = ff().free_identifier("s", None, Some(Type::pow(Type::Int)));
    assert_eq!(pred.wd_lemma_raw(), ff().simple_predicate(s, None));
}

#[test]
fn minimum_requires_a_nonempty_bounded_set() {
    let pred = checked(
        eq_pred(
            ff().unary_expression(UnaryExprOp::KMin, fid("s"), None),
            int(1),
        ),
        &env(&[("s", Type::pow(Type::Int))]),
    );
    let s = || ff().free_identifier("s", None, Some(Type::pow(Type::Int)));
    let empty = ff().atomic_expression(AtomicOp::EmptySet, None, Some(Type::pow(Type::Int)));
    let not_empty = ff().relational_predicate(RelationalOp::NotEqual, s(), empty, None);
    // ∃b · ∀x · x ∈ s ⇒ b ≤ x
    let b = ff().bound_identifier(1, None, Some(Type::Int));
    let x = || ff().bound_identifier(0, None, Some(Type::Int));
    let x_in_s = ff().relational_predicate(RelationalOp::In, x(), s(), None);
    let b_le_x = ff().relational_predicate(RelationalOp::Le, b, x(), None);
    let body = ff().binary_predicate(BinaryPredOp::LImp, x_in_s, b_le_x, None);
    let x_decl = ff().bound_ident_decl("x", None, None, Some(Type::Int));
    let inner = ff().quantified_predicate(QuantPredOp::Forall, vec![x_decl], body, None);
    let b_decl = ff().bound_ident_decl("b", None, None, Some(Type::Int));
    let bounded = ff().quantified_predicate(QuantPredOp::Exists, vec![b_decl], inner, None);
    let expected = ff().associative_predicate(AssocPredOp::LAnd, vec![not_empty, bounded], None);
    assert_eq!(pred.wd_lemma_raw(), expected);
}

// --- hypothesis loading ---

#[test]
fn conjunction_loads_left_conjuncts_as_hypotheses() {
    // a ≠ 0 ∧ 1 ÷ a = 1: the guard is discharged by the hypothesis.
    let environment = env(&[("a", Type::Int)]);
    let pred = checked(
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![
                ff().relational_predicate(RelationalOp::NotEqual, fid("a"), int(0), None),
                eq_pred(div(fid("a"), fid("a")), int(1)),
            ],
            None,
        ),
        &environment,
    );
    // L = ⊤ ∧ (a≠0 ⇒ a≠0) = ⊤
    assert_eq!(pred.wd_lemma_raw(), btrue());
}

#[test]
fn implication_loads_its_hypothesis() {
    // b ≠ 0 ⇒ 1 ÷ b = 1
    let pred = checked(
        ff().binary_predicate(
            BinaryPredOp::LImp,
            ff().relational_predicate(RelationalOp::NotEqual, fid("b"), int(0), None),
            eq_pred(div(int(1), fid("b")), int(1)),
            None,
        ),
        &env(&[("b", Type::Int)]),
    );
    assert_eq!(pred.wd_lemma_raw(), btrue());
}

#[test]
fn disjunction_folds_rightward() {
    // 1 ÷ a = 1 ∨ a = 0
    let pred = checked(
        ff().associative_predicate(
            AssocPredOp::LOr,
            vec![
                eq_pred(div(int(1), fid("a")), int(1)),
                eq_pred(fid("a"), int(0)),
            ],
            None,
        ),
        &env(&[("a", Type::Int)]),
    );
    // Folding right-to-left: the second disjunct contributes ⊤, and
    // lor absorbs it, leaving only the first disjunct's guard.
    let expected = ff().relational_predicate(RelationalOp::NotEqual, iid("a"), int(0), None);
    assert_eq!(pred.wd_lemma_raw(), expected);
}

// --- quantifiers ---

#[test]
fn quantifiers_close_the_lemma_universally() {
    // ∃s · s > 0 ⇒ 1 ÷ s = 1 still yields a ∀ lemma.
    let pred = checked(
        ff().quantified_predicate(
            QuantPredOp::Exists,
            vec![decl("s")],
            ff().binary_predicate(
                BinaryPredOp::LImp,
                ff().relational_predicate(RelationalOp::Gt, bid(0), int(0), None),
                eq_pred(div(int(1), bid(0)), int(1)),
                None,
            ),
            None,
        ),
        &env(&[]),
    );
    // ∀s · s > 0 ⇒ s ≠ 0
    let s_decl = ff().bound_ident_decl("s", None, None, Some(Type::Int));
    let ib = |i| ff().bound_identifier(i, None, Some(Type::Int));
    let body = ff().binary_predicate(
        BinaryPredOp::LImp,
        ff().relational_predicate(RelationalOp::Gt, ib(0), int(0), None),
        ff().relational_predicate(RelationalOp::NotEqual, ib(0), int(0), None),
        None,
    );
    let expected = ff().quantified_predicate(QuantPredOp::Forall, vec![s_decl], body, None);
    assert_eq!(pred.wd_lemma_raw(), expected);
}

#[test]
fn quantified_intersection_requires_a_witness() {
    // inter-like: ⋂x · x > 0 ∣ {x} — needs ∃x · x > 0.
    let cset = ff().quantified_expression(
        QuantExprOp::QInter,
        vec![decl("x")],
        ff().relational_predicate(RelationalOp::Gt, bid(0), int(0), None),
        ff().set_extension(vec![bid(0)], None),
        None,
        Form::Explicit,
    );
    let pred = checked(
        eq_pred(fid("s"), cset),
        &env(&[("s", Type::pow(Type::Int))]),
    );
    let x_decl = ff().bound_ident_decl("x", None, None, Some(Type::Int));
    let gt = ff().relational_predicate(
        RelationalOp::Gt,
        ff().bound_identifier(0, None, Some(Type::Int)),
        int(0),
        None,
    );
    let expected = ff().quantified_predicate(QuantPredOp::Exists, vec![x_decl], gt, None);
    assert_eq!(pred.wd_lemma_raw(), expected);
}

#[test]
fn vacuous_quantifiers_flatten_away() {
    // ∀x⦂ℤ · 1 ÷ y = 2: the lemma y ≠ 0 does not mention x, so the
    // universal closure loses its declaration and disappears. (The
    // declaration needs an annotation to type at all: it is unused.)
    let annotated = ff().bound_ident_decl(
        "x",
        None,
        Some(ff().atomic_expression(AtomicOp::Integer, None, None)),
        None,
    );
    let pred = checked(
        forall(vec![annotated], eq_pred(div(int(1), fid("y")), int(2))),
        &env(&[("y", Type::Int)]),
    );
    let expected = ff().relational_predicate(RelationalOp::NotEqual, iid("y"), int(0), None);
    assert_eq!(pred.wd_lemma_raw(), expected);
}

// --- assignments ---

#[test]
fn assignments_guard_their_formulas() {
    let environment = env(&[("x", Type::Int), ("y", Type::Int)]);

    let deterministic = ff().becomes_equal_to(vec![fid("x")], vec![div(int(1), fid("y"))], None);
    let typed = deterministic.type_check(&environment).typed.expect("typed");
    let expected = ff().relational_predicate(RelationalOp::NotEqual, iid("y"), int(0), None);
    assert_eq!(typed.wd_lemma_raw(), expected);

    // x :∣ x' = 1 ÷ x — the lemma binds the primed declaration... and
    // x ≠ 0 does not mention x', so the quantifier flattens away.
    let such_that = ff().becomes_such_that(
        vec![fid("x")],
        vec![decl("x'")],
        eq_pred(bid(0), div(int(1), fid("x"))),
        None,
    );
    let typed = such_that.type_check(&environment).typed.expect("typed");
    let expected = ff().relational_predicate(RelationalOp::NotEqual, iid("x"), int(0), None);
    assert_eq!(typed.wd_lemma_raw(), expected);
}

// --- strictness ---

#[test]
fn strictness_follows_the_operator_table() {
    let environment = env(&[("a", Type::Int)]);
    let guard = ff().relational_predicate(RelationalOp::NotEqual, fid("a"), int(0), None);
    let division = eq_pred(div(int(1), fid("a")), int(1));

    let conjunction = checked(
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![guard.clone(), division.clone()],
            None,
        ),
        &environment,
    );
    assert!(!conjunction.is_wd_strict());

    let equivalence = checked(
        ff().binary_predicate(BinaryPredOp::LEqv, guard.clone(), division.clone(), None),
        &environment,
    );
    assert!(equivalence.is_wd_strict());

    let implication = checked(
        ff().binary_predicate(BinaryPredOp::LImp, guard, division, None),
        &environment,
    );
    assert!(!implication.is_wd_strict());
    assert!(checked(eq_pred(fid("a"), int(1)), &environment).is_wd_strict());
}

#[test]
fn positional_strictness_requires_a_strict_path() {
    let environment = env(&[("a", Type::Int)]);
    // (1 ÷ a = 1) ⇔ (a ≠ 0): inside the equivalence everything is
    // reachable strictly; inside an implication nothing is.
    let equivalence = checked(
        ff().binary_predicate(
            BinaryPredOp::LEqv,
            eq_pred(div(int(1), fid("a")), int(1)),
            ff().relational_predicate(RelationalOp::NotEqual, fid("a"), int(0), None),
            None,
        ),
        &environment,
    );
    let left_left: rossi::formula::Position = "0.0".parse().expect("position");
    assert!(equivalence.is_wd_strict_at(&left_left));

    let implication = checked(
        ff().binary_predicate(
            BinaryPredOp::LImp,
            ff().relational_predicate(RelationalOp::NotEqual, fid("a"), int(0), None),
            eq_pred(div(int(1), fid("a")), int(1)),
            None,
        ),
        &environment,
    );
    assert!(!implication.is_wd_strict_at(&left_left));
    // The root itself is always reachable.
    assert!(implication.is_wd_strict_at(&rossi::formula::Position::root()));
}

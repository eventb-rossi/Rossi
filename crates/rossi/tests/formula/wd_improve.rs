//! Subsumption simplification of well-definedness lemmas.

use rossi::formula::tag::{
    AssocPredOp, BinaryExprOp, BinaryPredOp, QuantPredOp, RelationalOp, UnaryExprOp,
};
use rossi::formula::{Expression, Predicate, SealedTypeEnvironment, Type, TypeEnvironmentBuilder};

use crate::common::{decl, eq_pred, ff, fid, int};

fn btrue() -> Predicate {
    ff().literal_predicate(rossi::formula::tag::LiteralPredOp::BTrue, None)
}

/// An environment with a partial function `f ⦂ S ⇸ S` and elements of S.
fn fun_env() -> SealedTypeEnvironment {
    let mut builder = TypeEnvironmentBuilder::new();
    builder.add_given_set("S");
    builder.insert("f", Type::relation(Type::given("S"), Type::given("S")));
    builder.insert("a", Type::given("S"));
    builder.insert("b", Type::given("S"));
    builder.make_snapshot()
}

fn checked(pred: Predicate, environment: &SealedTypeEnvironment) -> Predicate {
    let result = pred.type_check(environment);
    assert!(result.is_success(), "problems: {:?}", result.problems);
    result.typed.expect("typed")
}

fn apply(f: &str, arg: Expression) -> Expression {
    ff().binary_expression(BinaryExprOp::FunImage, fid(f), arg, None)
}

/// Counts the top-level conjuncts of a lemma.
fn conjuncts(pred: &Predicate) -> usize {
    match pred.kind() {
        rossi::formula::PredicateKind::Associative { children, .. } => children.len(),
        _ => 1,
    }
}

#[test]
fn duplicate_guards_collapse() {
    // f(a) = f(b): both applications contribute `f ∈ S ⇸ S`; the
    // improved lemma keeps it once.
    let pred = checked(
        eq_pred(apply("f", fid("a")), apply("f", fid("b"))),
        &fun_env(),
    );
    let raw = pred.wd_lemma_raw();
    assert_eq!(conjuncts(&raw), 4);
    let improved = pred.wd_lemma();
    assert_eq!(conjuncts(&improved), 3);
}

#[test]
fn identical_applications_leave_one_guard_pair() {
    let pred = checked(
        eq_pred(apply("f", fid("a")), apply("f", fid("a"))),
        &fun_env(),
    );
    let improved = pred.wd_lemma();
    // a ∈ dom(f) ∧ f ∈ S ⇸ S
    assert_eq!(conjuncts(&improved), 2);
}

#[test]
fn hypotheses_subsume_their_conclusions() {
    // x ≠ 0 ⇒ (1÷x = 1 ∧ 2÷x = 2): every division guard is already
    // the hypothesis.
    let environment = {
        let mut builder = TypeEnvironmentBuilder::new();
        builder.insert("x", Type::Int);
        builder.make_snapshot()
    };
    let div = |num: i64| {
        eq_pred(
            ff().binary_expression(BinaryExprOp::Div, int(num), fid("x"), None),
            int(num),
        )
    };
    let pred = checked(
        ff().binary_predicate(
            BinaryPredOp::LImp,
            ff().relational_predicate(RelationalOp::NotEqual, fid("x"), int(0), None),
            ff().associative_predicate(AssocPredOp::LAnd, vec![div(1), div(2)], None),
            None,
        ),
        &environment,
    );
    assert_ne!(pred.wd_lemma_raw(), btrue());
    assert_eq!(pred.wd_lemma(), btrue());
}

#[test]
fn subsumption_reaches_across_binding_depths() {
    // f(a) = a ∧ (∀x · x ∈ dom(f) ⇒ f(x) = x): the functionality
    // guard `f ∈ S ⇸ S` inside the quantifier duplicates the outer
    // one, and the domain guard inside is its own hypothesis.
    let inner = ff().quantified_predicate(
        QuantPredOp::Forall,
        vec![decl("x")],
        ff().binary_predicate(
            BinaryPredOp::LImp,
            ff().relational_predicate(
                RelationalOp::In,
                ff().bound_identifier(0, None, None),
                ff().unary_expression(UnaryExprOp::KDom, fid("f"), None),
                None,
            ),
            eq_pred(
                apply("f", ff().bound_identifier(0, None, None)),
                ff().bound_identifier(0, None, None),
            ),
            None,
        ),
        None,
    );
    let pred = checked(
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![eq_pred(apply("f", fid("a")), fid("a")), inner],
            None,
        ),
        &fun_env(),
    );

    let improved = pred.wd_lemma();
    // Outer: a ∈ dom(f), f ∈ S ⇸ S. The inner implication's guards
    // are subsumed entirely, so nothing else survives.
    assert_eq!(conjuncts(&improved), 2, "got: {improved:?}");
}

#[test]
fn improvement_preserves_already_minimal_lemmas() {
    let pred = checked(
        eq_pred(
            ff().binary_expression(BinaryExprOp::Div, fid("a"), fid("b"), None),
            int(1),
        ),
        &{
            let mut builder = TypeEnvironmentBuilder::new();
            builder.insert("a", Type::Int);
            builder.insert("b", Type::Int);
            builder.make_snapshot()
        },
    );
    assert_eq!(pred.wd_lemma(), pred.wd_lemma_raw());
}

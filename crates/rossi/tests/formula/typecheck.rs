//! The two-pass type checker: solved types, inferred environments,
//! and problem reporting.

use rossi::formula::tag::{AssocPredOp, AtomicOp, BinaryExprOp, QuantExprOp, RelationalOp};
use rossi::formula::{
    Expression, Form, Predicate, ProblemKind, SealedTypeEnvironment, Type, TypeEnvironmentBuilder,
};

use crate::common::{bid, decl, eq_pred, ff, fid, forall, int};

fn env(bindings: &[(&str, Type)]) -> SealedTypeEnvironment {
    let mut builder = TypeEnvironmentBuilder::new();
    for (name, ty) in bindings {
        builder.insert(*name, ty.clone());
    }
    builder.make_snapshot()
}

fn member(left: Expression, right: Expression) -> Predicate {
    ff().relational_predicate(RelationalOp::In, left, right, None)
}

// --- success and inferred environments ---

#[test]
fn known_identifiers_get_their_environment_types() {
    let result = eq_pred(fid("x"), int(1)).type_check(&env(&[("x", Type::Int)]));
    assert!(result.is_success());
    let typed = result.typed.expect("typed rebuild");
    assert!(typed.is_type_checked());
    assert!(result.inferred.is_empty());

    // The rebuilt tree carries types on every expression node.
    match typed.kind() {
        rossi::formula::PredicateKind::Relational { left, right, .. } => {
            assert_eq!(left.ty(), Some(&Type::Int));
            assert_eq!(right.ty(), Some(&Type::Int));
        }
        _ => panic!("shape preserved"),
    }
}

#[test]
fn unknown_identifiers_are_inferred_in_first_occurrence_order() {
    // y = 1 ∧ s = {y}: y ⦂ ℤ, s ⦂ ℙ(ℤ), neither declared.
    let pred = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![
            eq_pred(fid("y"), int(1)),
            eq_pred(fid("s"), ff().set_extension(vec![fid("y")], None)),
        ],
        None,
    );
    let result = pred.type_check(&env(&[]));
    assert!(result.is_success(), "problems: {:?}", result.problems);
    let inferred: Vec<(&str, &Type)> = result.inferred.iter().collect();
    assert_eq!(inferred, [("y", &Type::Int), ("s", &Type::pow(Type::Int))]);
}

#[test]
fn inference_flows_through_equality_chains() {
    // x = y ∧ y = z ∧ z = 1 — everything is ℤ.
    let pred = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![
            eq_pred(fid("x"), fid("y")),
            eq_pred(fid("y"), fid("z")),
            eq_pred(fid("z"), int(1)),
        ],
        None,
    );
    let result = pred.type_check(&env(&[]));
    assert!(result.is_success());
    assert_eq!(result.inferred.get("x"), Some(&Type::Int));
    assert_eq!(result.inferred.get("y"), Some(&Type::Int));
    assert_eq!(result.inferred.get("z"), Some(&Type::Int));
}

#[test]
fn membership_types_the_element_from_the_set() {
    // e ∈ S with S a carrier set: e ⦂ S.
    let mut builder = TypeEnvironmentBuilder::new();
    builder.add_given_set("S");
    let result = member(fid("e"), fid("S")).type_check(&builder.make_snapshot());
    assert!(result.is_success());
    assert_eq!(result.inferred.get("e"), Some(&Type::given("S")));
}

#[test]
fn quantifier_bodies_type_their_declarations() {
    // ∀x · x ∈ ℕ: the declaration solves to ℤ.
    let pred = forall(
        vec![decl("x")],
        member(
            bid(0),
            ff().atomic_expression(AtomicOp::Natural, None, None),
        ),
    );
    let result = pred.type_check(&env(&[]));
    assert!(result.is_success());
    let typed = result.typed.expect("typed");
    match typed.kind() {
        rossi::formula::PredicateKind::Quantified { decls, .. } => {
            assert_eq!(decls[0].ty(), Some(&Type::Int));
            // The printing hint survives the rebuild.
            assert_eq!(decls[0].name(), "x");
        }
        _ => panic!("shape preserved"),
    }
}

#[test]
fn declaration_annotations_constrain_the_body() {
    // ∀x⦂ℤ · x = y infers y ⦂ ℤ from the annotation alone.
    let annotated = ff().bound_ident_decl(
        "x",
        None,
        Some(ff().atomic_expression(AtomicOp::Integer, None, None)),
        None,
    );
    let pred = forall(vec![annotated], eq_pred(bid(0), fid("y")));
    let result = pred.type_check(&env(&[]));
    assert!(result.is_success());
    assert_eq!(result.inferred.get("y"), Some(&Type::Int));
}

#[test]
fn ascriptions_are_checked_constraints() {
    // (x ⦂ ℤ) with x undeclared: x is inferred integer.
    let ascribed = ff().ascription(
        fid("x"),
        ff().atomic_expression(AtomicOp::Integer, None, None),
        None,
    );
    let result = ascribed.type_check(&env(&[]));
    assert!(result.is_success());
    assert_eq!(result.inferred.get("x"), Some(&Type::Int));

    // A contradicting ascription is a mismatch.
    let contradicted = ff().ascription(
        fid("b"),
        ff().atomic_expression(AtomicOp::Integer, None, None),
        None,
    );
    let result = contradicted.type_check(&env(&[("b", Type::Bool)]));
    assert_eq!(result.problems[0].kind, ProblemKind::TypesDoNotMatch);

    // An ascription whose right side is not a type spelling fails.
    let junk = ff().ascription(fid("x"), int(5), None);
    let result = junk.type_check(&env(&[]));
    assert!(!result.is_success());
}

#[test]
fn generic_atoms_solve_from_context() {
    // s = ∅ with s ⦂ ℙ(ℤ): the empty set solves to ℙ(ℤ).
    let pred = eq_pred(
        fid("s"),
        ff().atomic_expression(AtomicOp::EmptySet, None, None),
    );
    let result = pred.type_check(&env(&[("s", Type::pow(Type::Int))]));
    assert!(result.is_success());
    match result.typed.expect("typed").kind() {
        rossi::formula::PredicateKind::Relational { right, .. } => {
            assert_eq!(right.ty(), Some(&Type::pow(Type::Int)));
        }
        _ => panic!("shape preserved"),
    }
}

#[test]
fn expected_types_constrain_the_root() {
    let expr = ff().atomic_expression(AtomicOp::EmptySet, None, None);
    let expected = Type::pow(Type::Bool);
    let result = expr.type_check_with_expected(&env(&[]), &expected);
    assert!(result.is_success());
    assert_eq!(result.typed.expect("typed").ty(), Some(&expected));

    let mismatch = int(3).type_check_with_expected(&env(&[]), &Type::Bool);
    assert_eq!(mismatch.problems[0].kind, ProblemKind::TypesDoNotMatch);
}

#[test]
fn comprehensions_type_as_powersets() {
    // {x · x ∈ ℕ ∣ x} ⦂ ℙ(ℤ)
    let cset = ff().quantified_expression(
        QuantExprOp::CSet,
        vec![decl("x")],
        member(
            bid(0),
            ff().atomic_expression(AtomicOp::Natural, None, None),
        ),
        bid(0),
        None,
        Form::Explicit,
    );
    let result = cset.type_check(&env(&[]));
    assert!(result.is_success());
    assert_eq!(
        result.typed.expect("typed").ty(),
        Some(&Type::pow(Type::Int))
    );
}

// --- assignments ---

#[test]
fn assignments_type_targets_values_and_primes() {
    let environment = env(&[("x", Type::Int), ("y", Type::Bool)]);

    // x ≔ 1 checks; x ≔ TRUE does not.
    let good = ff().becomes_equal_to(vec![fid("x")], vec![int(1)], None);
    assert!(good.type_check(&environment).is_success());
    let bad = ff().becomes_equal_to(
        vec![fid("x")],
        vec![ff().atomic_expression(AtomicOp::True, None, None)],
        None,
    );
    assert!(!bad.type_check(&environment).is_success());

    // x, y :∈ S expects S ⦂ ℙ(ℤ × BOOL).
    let pair_set = ff().becomes_member_of(vec![fid("x"), fid("y")], fid("S"), None);
    let result = pair_set.type_check(&environment);
    assert!(result.is_success());
    assert_eq!(
        result.inferred.get("S"),
        Some(&Type::pow(Type::prod(Type::Int, Type::Bool)))
    );

    // x :∣ x' = x + … — the primed declaration shares x's type.
    let such_that = ff().becomes_such_that(
        vec![fid("x")],
        vec![decl("x'")],
        eq_pred(bid(0), fid("x")),
        None,
    );
    let result = such_that.type_check(&environment);
    assert!(result.is_success());
    match result.typed.expect("typed").kind() {
        rossi::formula::AssignmentKind::BecomesSuchThat { primed, .. } => {
            assert_eq!(primed[0].ty(), Some(&Type::Int));
        }
        _ => panic!("shape preserved"),
    }
}

// --- problems ---

#[test]
fn mismatches_are_reported_with_spans() {
    let spanned_int = ff().integer_literal(1, Some(rossi::ast::Span { start: 4, end: 5 }));
    let pred = ff().relational_predicate(
        RelationalOp::Lt,
        ff().atomic_expression(AtomicOp::True, None, None),
        spanned_int,
        None,
    );
    let result = pred.type_check(&env(&[]));
    assert!(!result.is_success());
    assert!(result.typed.is_none());
    assert_eq!(result.problems[0].kind, ProblemKind::TypesDoNotMatch);
}

#[test]
fn unsolved_identifiers_and_expressions_are_reported() {
    // x = y with neither declared: both stay unsolved.
    let result = eq_pred(fid("x"), fid("y")).type_check(&env(&[]));
    assert!(!result.is_success());
    assert!(
        result
            .problems
            .iter()
            .any(|p| p.kind == ProblemKind::UntypedIdentifier("x".into()))
    );
    // Inferred environments are only produced on success.
    assert!(result.inferred.is_empty());

    // ∅ = ∅ has no identifier to blame, only untypeable expressions.
    let empty = || ff().atomic_expression(AtomicOp::EmptySet, None, None);
    let result = eq_pred(empty(), empty()).type_check(&env(&[]));
    assert!(!result.is_success());
    assert!(
        result
            .problems
            .iter()
            .any(|p| p.kind == ProblemKind::UntypedExpression)
    );
}

#[test]
fn applications_never_type_check() {
    let pred = ff().predicate_application("p", None, vec![int(1)], None);
    let result = pred.type_check(&env(&[]));
    assert_eq!(result.problems[0].kind, ProblemKind::UncheckableApplication);
}

#[test]
fn dangling_bound_identifiers_are_reported() {
    let result = eq_pred(bid(0), int(1)).type_check(&env(&[]));
    assert!(
        result
            .problems
            .iter()
            .any(|p| p.kind == ProblemKind::DanglingBoundIdentifier)
    );
}

#[test]
fn circular_constraints_are_reported() {
    // x = {x}: x's type would contain itself.
    let pred = eq_pred(fid("x"), ff().set_extension(vec![fid("x")], None));
    let result = pred.type_check(&env(&[]));
    assert_eq!(result.problems[0].kind, ProblemKind::Circularity);
}

// --- idempotence and interplay with construction typing ---

#[test]
fn checking_a_typed_tree_is_stable() {
    let environment = env(&[("x", Type::Int)]);
    let once = eq_pred(fid("x"), int(1))
        .type_check(&environment)
        .typed
        .expect("typed");
    let twice = once.type_check(&environment).typed.expect("typed");
    assert_eq!(once, twice);
}

#[test]
fn shadowing_declarations_resolve_by_index() {
    // ∀x⦂ℤ · x = 1 ∧ (∀x⦂BOOL · x = TRUE): same hint, distinct types.
    let inner = forall(
        vec![ff().bound_ident_decl("x", None, None, Some(Type::Bool))],
        eq_pred(bid(0), ff().atomic_expression(AtomicOp::True, None, None)),
    );
    let outer = forall(
        vec![ff().bound_ident_decl("x", None, None, Some(Type::Int))],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![eq_pred(bid(0), int(1)), inner],
            None,
        ),
    );
    let result = outer.type_check(&env(&[]));
    assert!(result.is_success(), "problems: {:?}", result.problems);
}

#[test]
fn quantified_predicate_shapes_survive_the_rebuild() {
    // ∀a,b · a ∈ S ∧ f(a) ∈ T ∧ b ∈ S, over given sets S, T and a
    // relation f ⦂ ℙ(S × T).
    let mut builder = TypeEnvironmentBuilder::new();
    builder.add_given_set("S");
    builder.add_given_set("T");
    builder.insert("f", Type::relation(Type::given("S"), Type::given("T")));
    let environment = builder.make_snapshot();

    let pred = forall(
        vec![decl("a"), decl("b")],
        ff().associative_predicate(
            AssocPredOp::LAnd,
            vec![
                member(bid(1), fid("S")),
                member(
                    ff().binary_expression(BinaryExprOp::FunImage, fid("f"), bid(1), None),
                    fid("T"),
                ),
                member(bid(0), fid("S")),
            ],
            None,
        ),
    );
    let result = pred.type_check(&environment);
    assert!(result.is_success(), "problems: {:?}", result.problems);
    let typed = result.typed.expect("typed");
    match typed.kind() {
        rossi::formula::PredicateKind::Quantified { decls, .. } => {
            assert_eq!(decls[0].ty(), Some(&Type::given("S")));
            assert_eq!(decls[1].ty(), Some(&Type::given("S")));
        }
        _ => panic!("shape preserved"),
    }
}

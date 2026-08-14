//! Before-after and feasibility predicates, and type-expression
//! recognition.

use rossi::formula::tag::{
    AssocPredOp, AtomicOp, BinaryExprOp, QuantPredOp, RelationalOp, UnaryExprOp,
};
use rossi::formula::{Assignment, Expression, SealedTypeEnvironment, Type};

use crate::common::{bid, btrue, decl_ty, env, ff, fid, fid_ty};

/// Type-checks and returns the typed assignment.
fn checked_assign(assign: Assignment, environment: &SealedTypeEnvironment) -> Assignment {
    let result = assign.type_check(environment);
    assert!(result.is_success(), "problems: {:?}", result.problems);
    result.typed.expect("typed")
}

fn int_env() -> SealedTypeEnvironment {
    env(&[("x", Type::Int), ("y", Type::Int)])
}

// --- becomes-equal-to ---

#[test]
fn deterministic_single_target_equates_the_primed_identifier() {
    // x ≔ y
    let assign = checked_assign(
        ff().becomes_equal_to(vec![fid("x")], vec![fid("y")], None),
        &int_env(),
    );
    let expected = ff().relational_predicate(
        RelationalOp::Equal,
        fid_ty("x'", Type::Int),
        fid_ty("y", Type::Int),
        None,
    );
    assert_eq!(assign.ba_predicate(), expected);
    assert_eq!(assign.fis_predicate(), btrue());
}

#[test]
fn deterministic_multi_target_conjoins_the_equalities() {
    // x, y ≔ y, x
    let assign = checked_assign(
        ff().becomes_equal_to(vec![fid("x"), fid("y")], vec![fid("y"), fid("x")], None),
        &int_env(),
    );
    let eq = |left: Expression, right: Expression| {
        ff().relational_predicate(RelationalOp::Equal, left, right, None)
    };
    let expected = ff().associative_predicate(
        AssocPredOp::LAnd,
        vec![
            eq(fid_ty("x'", Type::Int), fid_ty("y", Type::Int)),
            eq(fid_ty("y'", Type::Int), fid_ty("x", Type::Int)),
        ],
        None,
    );
    assert_eq!(assign.ba_predicate(), expected);
}

// --- becomes-member-of ---

#[test]
fn member_of_relates_the_primed_identifier_to_the_set() {
    // x :∈ S
    let set_ty = Type::pow(Type::Int);
    let environment = env(&[("x", Type::Int), ("S", set_ty.clone())]);
    let assign = checked_assign(
        ff().becomes_member_of(vec![fid("x")], fid("S"), None),
        &environment,
    );
    let expected = ff().relational_predicate(
        RelationalOp::In,
        fid_ty("x'", Type::Int),
        fid_ty("S", set_ty.clone()),
        None,
    );
    assert_eq!(assign.ba_predicate(), expected);

    // FIS: S ≠ ∅, with the empty set typed like S.
    let empty = ff().atomic_expression(AtomicOp::EmptySet, None, Some(set_ty.clone()));
    let fis = ff().relational_predicate(RelationalOp::NotEqual, fid_ty("S", set_ty), empty, None);
    assert_eq!(assign.fis_predicate(), fis);
}

#[test]
fn member_of_multi_target_pairs_the_primed_identifiers() {
    // x, y :∈ S  with  S ⊆ ℤ × ℤ
    let set_ty = Type::pow(Type::prod(Type::Int, Type::Int));
    let environment = env(&[("x", Type::Int), ("y", Type::Int), ("S", set_ty.clone())]);
    let assign = checked_assign(
        ff().becomes_member_of(vec![fid("x"), fid("y")], fid("S"), None),
        &environment,
    );
    let pair = ff().binary_expression(
        BinaryExprOp::Mapsto,
        fid_ty("x'", Type::Int),
        fid_ty("y'", Type::Int),
        None,
    );
    let expected = ff().relational_predicate(RelationalOp::In, pair, fid_ty("S", set_ty), None);
    assert_eq!(assign.ba_predicate(), expected);
}

// --- becomes-such-that ---

#[test]
fn such_that_frees_the_primed_declarations() {
    // x :∣ x' = x, with the condition scoped under the primed binder.
    let condition = ff().relational_predicate(
        RelationalOp::Equal,
        ff().bound_identifier(0, None, Some(Type::Int)),
        fid("x"),
        None,
    );
    let assign = checked_assign(
        ff().becomes_such_that(
            vec![fid("x")],
            vec![decl_ty("x'", Type::Int)],
            condition,
            None,
        ),
        &int_env(),
    );

    // BA: the bound x' becomes the free identifier x'.
    let expected = ff().relational_predicate(
        RelationalOp::Equal,
        fid_ty("x'", Type::Int),
        fid_ty("x", Type::Int),
        None,
    );
    assert_eq!(assign.ba_predicate(), expected);

    // FIS: ∃x' · x' = x, with the binder intact.
    let body = ff().relational_predicate(
        RelationalOp::Equal,
        ff().bound_identifier(0, None, Some(Type::Int)),
        fid_ty("x", Type::Int),
        None,
    );
    let fis = ff().quantified_predicate(
        QuantPredOp::Exists,
        vec![decl_ty("x'", Type::Int)],
        body,
        None,
    );
    assert_eq!(assign.fis_predicate(), fis);
}

#[test]
fn such_that_instantiation_respects_inner_binders() {
    // x :∣ ∀y · y = x'  — the condition's x' sits under another binder.
    let inner_body = ff().relational_predicate(
        RelationalOp::Equal,
        ff().bound_identifier(0, None, Some(Type::Int)),
        ff().bound_identifier(1, None, Some(Type::Int)),
        None,
    );
    let condition = ff().quantified_predicate(
        QuantPredOp::Forall,
        vec![decl_ty("y", Type::Int)],
        inner_body,
        None,
    );
    let assign = checked_assign(
        ff().becomes_such_that(
            vec![fid("x")],
            vec![decl_ty("x'", Type::Int)],
            condition,
            None,
        ),
        &int_env(),
    );

    let expected_body = ff().relational_predicate(
        RelationalOp::Equal,
        ff().bound_identifier(0, None, Some(Type::Int)),
        fid_ty("x'", Type::Int),
        None,
    );
    let expected = ff().quantified_predicate(
        QuantPredOp::Forall,
        vec![decl_ty("y", Type::Int)],
        expected_body,
        None,
    );
    assert_eq!(assign.ba_predicate(), expected);
}

// --- type expressions ---

#[test]
fn base_type_expressions_are_recognized() {
    assert!(
        ff().atomic_expression(AtomicOp::Integer, None, None)
            .is_type_expression()
    );
    assert!(
        ff().atomic_expression(AtomicOp::Bool, None, None)
            .is_type_expression()
    );
    // A carrier set denotes its own type.
    let carrier = fid_ty("S", Type::pow(Type::Given("S".to_string())));
    assert!(carrier.is_type_expression());
}

#[test]
fn compound_type_expressions_are_recognized() {
    let s = fid_ty("S", Type::pow(Type::Given("S".to_string())));
    let t = fid_ty("T", Type::pow(Type::Given("T".to_string())));
    let pow = ff().unary_expression(UnaryExprOp::Pow, s.clone(), None);
    assert!(pow.is_type_expression());
    let cprod = ff().binary_expression(BinaryExprOp::CProd, s.clone(), t.clone(), None);
    assert!(cprod.is_type_expression());
    let rel = ff().binary_expression(BinaryExprOp::Rel, s, t, None);
    assert!(rel.is_type_expression());
}

#[test]
fn non_type_expressions_are_rejected() {
    // ℕ is a set, not a type.
    assert!(
        !ff()
            .atomic_expression(AtomicOp::Natural, None, None)
            .is_type_expression()
    );
    // An integer identifier is a value.
    assert!(!fid_ty("x", Type::Int).is_type_expression());
    // A set identifier whose type names a different carrier set.
    let alias = fid_ty("S", Type::pow(Type::Given("T".to_string())));
    assert!(!alias.is_type_expression());
    // An untyped identifier.
    assert!(!fid("S").is_type_expression());
    // A set extension over a type.
    let members = ff().set_extension(vec![fid_ty("x", Type::Int)], None);
    assert!(!members.is_type_expression());
    // A product with one non-type side.
    let s = fid_ty("S", Type::pow(Type::Given("S".to_string())));
    let half = ff().binary_expression(BinaryExprOp::CProd, s, fid_ty("x", Type::Int), None);
    assert!(!half.is_type_expression());
    // A bound identifier.
    assert!(!bid(0).is_type_expression());
}

//! The static checker's single identifier-typing seam.
//!
//! Constants, variables and event parameters are all typed the same
//! way: a fixpoint over the component's typing predicates that types
//! as many of the declared names as possible, leaving the caller to
//! diagnose the rest.
//!
//! The engine behind the seam is the formula model's type checker:
//! each predicate is lowered onto the typed model and checked against
//! the current environment; on success, the types it infers for
//! declared names are merged and the fixpoint continues until nothing
//! new resolves. A predicate that infers a name outside the declared
//! set references an unknown identifier — its typings are not trusted,
//! exactly as the previous engine refused predicates it could not
//! fully verify.

use rossi::formula::lower::{lower_action, lower_expression, lower_predicate};
use rossi::formula::{self, TypeEnvironmentBuilder};
use rossi::{Action, Expression, Predicate};

use crate::type_env::TypeEnv;

/// Types the `declared` names against `predicates`, inserting solved
/// types into `env`; returns the names that remained untyped, in
/// declaration order.
pub(crate) fn resolve_identifier_types<'a>(
    env: &mut TypeEnv,
    declared: &'a [String],
    predicates: &[Predicate],
) -> Vec<&'a str> {
    let lowered: Vec<formula::Predicate> = predicates.iter().map(lower_predicate).collect();
    loop {
        let mut progressed = false;
        let sealed = seal(env);
        for pred in &lowered {
            let result = pred.type_check(&sealed);
            if !result.is_success() {
                continue;
            }
            // Reject typings from predicates referencing identifiers
            // that are neither in the environment nor declared here.
            if result
                .inferred
                .iter()
                .any(|(name, _)| !declared.iter().any(|d| d == name))
            {
                continue;
            }
            for (name, ty) in result.inferred.iter() {
                if !env.contains(name) {
                    env.insert(name, ty.clone());
                    progressed = true;
                }
            }
        }
        if !progressed {
            break;
        }
    }
    declared
        .iter()
        .filter(|name| !env.contains(name))
        .map(String::as_str)
        .collect()
}

/// The per-formula gate and its payoff in one step: the fully typed
/// formula-model rebuild of the predicate, or `None` when it does not
/// type-check against `env` without deriving anything new — an
/// identifier the environment does not know makes the formula
/// unverifiable.
pub(crate) fn typed_predicate(env: &TypeEnv, pred: &Predicate) -> Option<formula::Predicate> {
    let result = lower_predicate(pred).type_check(&seal(env));
    (result.is_success() && result.inferred.is_empty()).then(|| {
        result
            .typed
            .expect("a successful check produces the rebuild")
    })
}

/// See [`typed_predicate`].
pub(crate) fn typed_expression(env: &TypeEnv, expr: &Expression) -> Option<formula::Expression> {
    let result = lower_expression(expr).type_check(&seal(env));
    (result.is_success() && result.inferred.is_empty()).then(|| {
        result
            .typed
            .expect("a successful check produces the rebuild")
    })
}

/// See [`typed_predicate`]. `None` also stands for `skip`, which has
/// no assignment to rebuild (and nothing to check).
pub(crate) fn typed_assignment(env: &TypeEnv, action: &Action) -> Option<formula::Assignment> {
    let result = lower_action(action)?.type_check(&seal(env));
    (result.is_success() && result.inferred.is_empty()).then(|| {
        result
            .typed
            .expect("a successful check produces the rebuild")
    })
}

/// See [`typed_predicate`]. `skip` has nothing to check.
pub(crate) fn action_well_typed(env: &TypeEnv, action: &Action) -> bool {
    match lower_action(action) {
        Some(assignment) => {
            let result = assignment.type_check(&seal(env));
            result.is_success() && result.inferred.is_empty()
        }
        None => true,
    }
}

/// The checker-facing snapshot of the pipeline's environment.
pub(crate) fn seal(env: &TypeEnv) -> formula::SealedTypeEnvironment {
    let mut builder = TypeEnvironmentBuilder::new();
    for (name, ty) in env.iter() {
        builder.insert(name, ty.clone());
    }
    builder.make_snapshot()
}

#[cfg(test)]
mod tests {
    use super::*;
    use rossi::ast::expression::{BinaryOp, UnaryOp};
    use rossi::formula::Type;
    use rossi::{parse_action_str, parse_expression_str, parse_predicate_str};

    fn carrier_elem(name: &str) -> Type {
        Type::Given(name.to_string())
    }

    fn auction_env() -> TypeEnv {
        let mut env = TypeEnv::new();
        env.add_carrier_set("AUCTIONS");
        env.add_carrier_set("ITEMS");
        env.insert(
            "a",
            Type::prod(carrier_elem("AUCTIONS"), carrier_elem("ITEMS")),
        );
        env.insert("i", carrier_elem("ITEMS"));
        env.insert("item", Type::pow(carrier_elem("ITEMS")));
        env.insert(
            "auctions",
            Type::relation(carrier_elem("AUCTIONS"), carrier_elem("ITEMS")),
        );
        env
    }

    #[test]
    fn rejects_membership_with_pair_rhs() {
        let env = auction_env();
        let p = parse_predicate_str("a ∈ AUCTIONS ↦ item").unwrap();
        assert!(typed_predicate(&env, &p).is_none());
    }

    #[test]
    fn rejects_assignment_with_mismatched_union_operands() {
        let env = auction_env();
        let a = parse_action_str("auctions ≔ auctions ∪ {a ↦ i}").unwrap();
        assert!(!action_well_typed(&env, &a));
    }

    #[test]
    fn accepts_membership_with_set_rhs() {
        let env = auction_env();
        let p = parse_predicate_str("a ∈ auctions").unwrap();
        assert!(typed_predicate(&env, &p).is_some());
    }

    #[test]
    fn accepts_assignment_with_consistent_types() {
        let env = auction_env();
        let a = parse_action_str("auctions ≔ auctions ∪ {a}").unwrap();
        assert!(action_well_typed(&env, &a));
    }

    #[test]
    fn rejects_non_integer_arithmetic_operands() {
        let env = TypeEnv::new();
        for source in [
            "TRUE + FALSE",
            "TRUE − FALSE",
            "TRUE ∗ FALSE",
            "TRUE ÷ FALSE",
            "TRUE mod FALSE",
            "TRUE ^ FALSE",
            "TRUE ‥ FALSE",
            "−TRUE",
        ] {
            let expression = parse_expression_str(source).unwrap();
            assert!(
                typed_expression(&env, &expression).is_none(),
                "accepted ill-typed arithmetic expression: {source}"
            );
        }
    }

    #[test]
    fn rejects_invalid_set_and_relation_operands() {
        let env = TypeEnv::new();
        for op in [
            BinaryOp::Union,
            BinaryOp::Intersection,
            BinaryOp::Difference,
            BinaryOp::CartesianProduct,
            BinaryOp::Relation,
            BinaryOp::TotalRelation,
            BinaryOp::SurjectiveRelation,
            BinaryOp::TotalSurjectiveRelation,
            BinaryOp::TotalFunction,
            BinaryOp::PartialFunction,
            BinaryOp::TotalInjection,
            BinaryOp::PartialInjection,
            BinaryOp::TotalSurjection,
            BinaryOp::PartialSurjection,
            BinaryOp::Bijection,
            BinaryOp::Composition,
            BinaryOp::Semicolon,
            BinaryOp::DomainRestriction,
            BinaryOp::DomainSubtraction,
            BinaryOp::RangeRestriction,
            BinaryOp::RangeSubtraction,
            BinaryOp::Overwrite,
            BinaryOp::DirectProduct,
            BinaryOp::ParallelProduct,
        ] {
            let expression = rossi::ExpressionKind::Binary {
                op,
                left: Box::new(rossi::ExpressionKind::True.into()),
                right: Box::new(rossi::ExpressionKind::False.into()),
            }
            .into();
            assert!(
                typed_expression(&env, &expression).is_none(),
                "accepted ill-typed set/relation operator: {op:?}"
            );
        }

        for op in [
            UnaryOp::PowerSet,
            UnaryOp::PowerSet1,
            UnaryOp::Domain,
            UnaryOp::Range,
            UnaryOp::Inverse,
        ] {
            let expression = rossi::ExpressionKind::Unary {
                op,
                operand: Box::new(rossi::ExpressionKind::True.into()),
            }
            .into();
            assert!(
                typed_expression(&env, &expression).is_none(),
                "accepted ill-typed unary operator: {op:?}"
            );
        }
    }

    #[test]
    fn rejects_nested_structural_operand_failures() {
        let mut env = TypeEnv::new();
        env.insert("S", Type::pow(Type::Int));
        env.insert("r", Type::relation(Type::Int, Type::Int));

        for source in ["S ∪ dom(TRUE)", "dom(TRUE) ◁ r"] {
            let expression = parse_expression_str(source).unwrap();
            assert!(
                typed_expression(&env, &expression).is_none(),
                "accepted nested ill-typed expression: {source}"
            );
        }
    }

    #[test]
    fn rejects_invalid_comparison_operands() {
        let env = TypeEnv::new();
        for source in [
            "TRUE = 0",
            "TRUE ≠ 0",
            "TRUE < FALSE",
            "TRUE ≤ FALSE",
            "TRUE > FALSE",
            "TRUE ≥ FALSE",
            "0 ∈ BOOL",
            "0 ∉ BOOL",
            "BOOL ⊆ ℤ",
            "BOOL ⊂ ℤ",
            "BOOL ⊈ ℤ",
            "BOOL ⊄ ℤ",
            "finite(TRUE)",
            "partition(BOOL, {0})",
        ] {
            let predicate = parse_predicate_str(source).unwrap();
            assert!(
                !typed_predicate(&env, &predicate).is_some(),
                "accepted ill-typed predicate: {source}"
            );
        }
    }

    #[test]
    fn rejects_invalid_function_applications() {
        let mut env = TypeEnv::new();
        env.insert("f", Type::relation(Type::Int, Type::Bool));
        for source in [
            "f(TRUE)",
            "TRUE(0)",
            "f[{TRUE}]",
            "card(TRUE)",
            "min({TRUE})",
            "max({TRUE})",
            "union({TRUE})",
            "inter({TRUE})",
        ] {
            let expression = parse_expression_str(source).unwrap();
            assert!(
                typed_expression(&env, &expression).is_none(),
                "accepted ill-typed application: {source}"
            );
        }
    }

    #[test]
    fn rejects_assignment_type_mismatches() {
        let mut env = TypeEnv::new();
        env.insert("x", Type::Int);

        for source in ["x ≔ TRUE", "x :∈ BOOL", "x :∣ x' = TRUE"] {
            let action = parse_action_str(source).unwrap();
            assert!(
                !action_well_typed(&env, &action),
                "accepted ill-typed assignment: {source}"
            );
        }

        for source in ["x ≔ 0", "x :∈ ℤ", "x :∣ x' = x"] {
            let action = parse_action_str(source).unwrap();
            assert!(
                action_well_typed(&env, &action),
                "rejected well-typed assignment: {source}"
            );
        }
    }

    #[test]
    fn rejects_invalid_quantified_and_binder_bodies() {
        let env = TypeEnv::new();
        let predicate = parse_predicate_str("∀x⦂ℤ · x + TRUE = 0").unwrap();
        assert!(typed_predicate(&env, &predicate).is_none());

        for source in [
            "λx⦂ℤ·x = x ∣ x + TRUE",
            "{x⦂ℤ·x = x ∣ x + TRUE}",
            "{x⦂ℤ ∣ x + TRUE = 0}",
            "{bool(x ∈ ℤ) ∣ x ∈ ℤ ∧ x + TRUE = 0}",
            "⋃x⦂ℤ·x = x ∣ x + TRUE",
            "⋂x⦂ℤ·x = x ∣ x + TRUE",
            "bool(TRUE + FALSE = 0)",
            "{TRUE, 0}",
            "TRUE ⦂ ℤ",
        ] {
            let expression = parse_expression_str(source).unwrap();
            assert!(
                typed_expression(&env, &expression).is_none(),
                "accepted ill-typed binder expression: {source}"
            );
        }
    }

    #[test]
    fn accepts_valid_quantified_binders_and_function_applications() {
        let mut env = TypeEnv::new();
        env.insert("f", Type::relation(Type::Int, Type::Bool));

        let predicate = parse_predicate_str("∀x⦂ℤ · x + 1 > x").unwrap();
        assert!(typed_predicate(&env, &predicate).is_some());

        for source in [
            "f(0)",
            "λx⦂ℤ·x = x ∣ x + 1",
            "{x⦂ℤ·x = x ∣ x + 1}",
            "⋃x⦂ℤ·x = x ∣ {x}",
        ] {
            let expression = parse_expression_str(source).unwrap();
            assert!(
                typed_expression(&env, &expression).is_some(),
                "rejected well-typed binder expression: {source}"
            );
        }
    }

    #[test]
    fn accepts_binder_types_from_buried_and_chained_constraints() {
        let env = TypeEnv::new();
        for source in [
            "∀x·x + 1 > 0",
            "∀x·⊤ ⇒ x + 1 > 0",
            "∀x·⊥ ∨ x + 1 > 0",
            "∀x,y,z·x = y ∧ y = z ∧ z = 1",
        ] {
            let predicate = parse_predicate_str(source).unwrap();
            assert!(
                typed_predicate(&env, &predicate).is_some(),
                "rejected well-typed binder predicate: {source}"
            );
        }
    }

    #[test]
    fn assignment_expected_type_resolves_polymorphic_rhs() {
        let mut env = TypeEnv::new();
        env.insert("f", Type::relation(Type::Int, Type::Int));
        env.insert("S", Type::pow(Type::Int));

        for source in ["f ≔ λx·1 = 1 ∣ x + 1", "S ≔ union(∅)"] {
            let action = parse_action_str(source).unwrap();
            assert!(
                action_well_typed(&env, &action),
                "rejected contextually typed assignment: {source}"
            );
        }
    }

    #[test]
    fn unresolved_polymorphic_predicates_are_not_reported_as_checked() {
        let env = TypeEnv::new();
        for source in ["∅ = ∅", "id = id", "finite(∅)"] {
            let predicate = parse_predicate_str(source).unwrap();
            assert!(
                !typed_predicate(&env, &predicate).is_some(),
                "accepted predicate with unresolved types: {source}"
            );
        }
    }

    #[test]
    fn unresolved_operands_are_not_reported_as_checked() {
        let mut env = TypeEnv::new();
        env.insert("S", Type::pow(Type::Int));
        let expression = parse_expression_str("S ∪ unknown").unwrap();
        assert!(typed_expression(&env, &expression).is_none());
    }
}

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

use rossi::Predicate;
use rossi::formula::lower::lower_predicate;
use rossi::formula::{self, TypeEnvironmentBuilder};

use crate::type_env::TypeEnv;
use crate::types::Type;

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
                    env.insert(name, from_model(ty));
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

/// The checker-facing snapshot of the pipeline's environment.
pub(crate) fn seal(env: &TypeEnv) -> formula::SealedTypeEnvironment {
    let mut builder = TypeEnvironmentBuilder::new();
    for (name, ty) in env.iter() {
        builder.insert(name, to_model(ty));
    }
    builder.make_snapshot()
}

/// The pipeline's type for a model type. Parametric types cannot occur:
/// the core-language factory has no type constructors.
pub(crate) fn from_model(ty: &formula::Type) -> Type {
    match ty {
        formula::Type::Bool => Type::Boolean,
        formula::Type::Int => Type::Integer,
        formula::Type::Given(name) => Type::GivenSet(name.clone()),
        formula::Type::Pow(inner) => Type::pow(from_model(inner)),
        formula::Type::Prod(left, right) => Type::prod(from_model(left), from_model(right)),
        formula::Type::Parametric { symbol, .. } => {
            unreachable!("no type constructors in the core language: {symbol}")
        }
    }
}

/// The model type for a pipeline type.
pub(crate) fn to_model(ty: &Type) -> formula::Type {
    match ty {
        Type::Boolean => formula::Type::Bool,
        Type::Integer => formula::Type::Int,
        Type::GivenSet(name) => formula::Type::given(name.clone()),
        Type::PowerSet(inner) => formula::Type::pow(to_model(inner)),
        Type::Product(left, right) => formula::Type::prod(to_model(left), to_model(right)),
    }
}

//! The static checker's single identifier-typing seam.
//!
//! Constants, variables and event parameters are all typed the same
//! way: a fixpoint over the component's typing predicates that types
//! as many of the declared names as possible, leaving the caller to
//! diagnose the rest. Every pipeline stage resolves declaration types
//! through this one entry point, so the inference engine behind it can
//! be replaced without touching the call sites.

use rossi::Predicate;

use crate::infer::infer_constants;
use crate::type_env::TypeEnv;

/// Types the `declared` names against `predicates`, inserting solved
/// types into `env`; returns the names that remained untyped, in
/// declaration order.
pub(crate) fn resolve_identifier_types<'a>(
    env: &mut TypeEnv,
    declared: &'a [String],
    predicates: &[Predicate],
) -> Vec<&'a str> {
    infer_constants(env, declared, predicates)
}

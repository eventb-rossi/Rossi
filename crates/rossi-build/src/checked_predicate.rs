//! Unified per-element checker: free-identifier scan + typed rebuild
//! in one call.
//!
//! Every static-checker call site that handles a labeled predicate
//! (axiom, invariant, guard, witness) needs the same two verdicts —
//! "is it closed against the environment" and "does it type-check" —
//! plus the typed rebuild itself. This module gives them one entry
//! point, so the "check then record" recipe doesn't have to be
//! open-coded everywhere. Canonical text is no longer part of the
//! result: the render layer derives it from the typed rebuild at
//! emission time.
//!
//! Action checking additionally surfaces the first free identifier on
//! the action's read side (RHS of `:=`, set of `:∈`, predicate of
//! `:|`, arguments + RHS of `f(x) := …`) for callers that want to
//! emit a diagnostic. LHS variable names are *not* checked here: they
//! are the write targets, and the SC validates them via the variable
//! table.

use rossi::{Action, Expression, LabeledPredicate, Predicate};

use crate::sc::identifier_walker::{
    free_identifier_in_action_rhs, free_identifier_in_expression, free_identifier_in_predicate,
    usage_span_in_predicate,
};
use crate::type_env::TypeEnv;
use crate::{Diagnostic, Severity};

/// Result of checking a labeled predicate.
#[derive(Debug, Clone)]
pub struct PredicateCheck {
    /// The predicate the check ran on. Kept on guard/axiom decls, where
    /// descendant (M1+) static checks re-read it to re-derive parameter
    /// types for extended events.
    pub predicate: Predicate,
    /// First identifier in the predicate that is neither in `env` nor
    /// bound by a local quantifier / lambda / set-comprehension. `None`
    /// iff the predicate is closed against `env`.
    pub free_identifier: Option<String>,
    /// The fully typed formula-model rebuild, when the predicate
    /// type-checks against `env`. `None` is the ill-typed verdict.
    pub typed: Option<rossi::formula::Predicate>,
}

/// Result of checking a standalone expression (currently only used by
/// the variant). Same shape as [`PredicateCheck`].
#[derive(Debug, Clone)]
pub struct ExpressionCheck {
    pub expression: Expression,
    pub free_identifier: Option<String>,
    /// See [`PredicateCheck::typed`].
    pub typed: Option<rossi::formula::Expression>,
}

/// Result of checking an action.
#[derive(Debug, Clone)]
pub struct ActionCheck {
    /// The action the check ran on (see [`PredicateCheck::predicate`]).
    pub action: Action,
    /// First free identifier on the action's read side. `None` iff
    /// every read identifier is in `env` (or a built-in).
    pub free_identifier: Option<String>,
    /// The fully typed formula-model rebuild, when the action is an
    /// assignment that type-checks against `env`. `None` for `skip`
    /// and for ill-typed assignments; the action gate distinguishes
    /// the two through the seam.
    pub typed: Option<rossi::formula::Assignment>,
}

/// Check a predicate against `env`: the free-identifier scan and the
/// typed rebuild.
pub fn check_predicate(p: &Predicate, env: &TypeEnv) -> PredicateCheck {
    PredicateCheck {
        free_identifier: free_identifier_in_predicate(p, env),
        typed: crate::sc::typing::typed_predicate(env, p),
        predicate: p.clone(),
    }
}

/// Check an expression against `env`. Used by the variant.
pub fn check_expression(e: &Expression, env: &TypeEnv) -> ExpressionCheck {
    ExpressionCheck {
        free_identifier: free_identifier_in_expression(e, env),
        typed: crate::sc::typing::typed_expression(env, e),
        expression: e.clone(),
    }
}

/// Check an action against `env`. Walks every read-side expression and
/// (for `:|`) the becomes-such-that predicate.
pub fn check_action(a: &Action, env: &TypeEnv) -> ActionCheck {
    ActionCheck {
        free_identifier: free_identifier_in_action_rhs(a, env),
        typed: crate::sc::typing::typed_assignment(env, a),
        action: a.clone(),
    }
}

/// Resolve a labeled predicate against `env` and produce the effective
/// label plus the full [`PredicateCheck`], or a [`Diagnostic`] if the
/// predicate references an unknown identifier.
///
/// This is the shared shape of axiom / invariant / guard checking:
///
/// - `default_label` is what we substitute when the source had no
///   label (Rodin uses `axm` / `inv` / `grd`; we follow suit).
/// - `kind_name` is the human-readable element type used in the
///   diagnostic message (e.g. `"axiom"` → "unknown identifier 'x' in
///   axiom predicate").
/// - `origin` builds the dotted origin string from the *effective*
///   label (`{ctx}.{lbl}`, `{mach}.{lbl}`, `{mach}.{event}.{lbl}`
///   are the three current shapes).
///
/// The caller does its own URI minting and decl construction — this
/// helper owns only the bits that are common to all three sites.
pub fn check_labeled_predicate(
    raw: &LabeledPredicate,
    env: &TypeEnv,
    default_label: &str,
    kind_name: &str,
    origin: impl FnOnce(&str) -> String,
) -> std::result::Result<(String, PredicateCheck), Diagnostic> {
    let pc = check_predicate(&raw.predicate, env);
    let label = raw
        .label
        .clone()
        .unwrap_or_else(|| default_label.to_string());
    if let Some(bad) = &pc.free_identifier {
        // Anchor on the offending identifier; fall back to the labeled
        // predicate's own span.
        let span = usage_span_in_predicate(&raw.predicate, bad).or(raw.span);
        return Err(Diagnostic {
            severity: Severity::Error,
            origin: origin(&label),
            message: format!("unknown identifier '{bad}' in {kind_name} predicate"),
            rule_id: Some(crate::RuleId::UndeclaredIdentifier),
            span,
        });
    }
    if pc.typed.is_none() {
        return Err(Diagnostic {
            severity: Severity::Error,
            origin: origin(&label),
            message: format!("{kind_name} predicate is ill-typed"),
            rule_id: Some(crate::RuleId::TypeError),
            span: raw.span,
        });
    }
    Ok((label, pc))
}

#[cfg(test)]
mod tests {
    use super::*;
    use rossi::formula::Type;
    use rossi::{parse_action_str, parse_expression_str, parse_predicate_str};

    fn env_with_users() -> TypeEnv {
        let mut env = TypeEnv::new();
        env.add_carrier_set("USERS");
        env.insert("n", Type::Int);
        env
    }

    #[test]
    fn predicate_types_and_finds_no_free_when_closed() {
        let env = env_with_users();
        let p = parse_predicate_str("n ∈ ℕ").unwrap();
        let pc = check_predicate(&p, &env);
        assert!(pc.typed.is_some());
        assert_eq!(pc.free_identifier, None);
    }

    #[test]
    fn predicate_surfaces_first_free_identifier() {
        let env = env_with_users();
        let p = parse_predicate_str("alice ∈ USERS").unwrap();
        let pc = check_predicate(&p, &env);
        assert_eq!(pc.free_identifier.as_deref(), Some("alice"));
        assert!(pc.typed.is_none(), "an unknown identifier is unverifiable");
    }

    #[test]
    fn expression_check_threads_through() {
        let env = env_with_users();
        let e = parse_expression_str("n + 1").unwrap();
        let ec = check_expression(&e, &env);
        assert_eq!(ec.free_identifier, None);
        assert!(ec.typed.is_some());
    }

    #[test]
    fn action_check_skips_lhs_variable() {
        let mut env = TypeEnv::new();
        env.insert("x", Type::pow(Type::Given("USERS".into())));
        let a = parse_action_str("x ≔ ∅").unwrap();
        let ac = check_action(&a, &env);
        // `x` is the LHS — must not be flagged. `∅` is a literal.
        assert_eq!(ac.free_identifier, None);
        assert!(ac.typed.is_some());
    }

    #[test]
    fn action_check_flags_unknown_rhs_identifier() {
        let mut env = TypeEnv::new();
        env.insert("x", Type::Int);
        let a = parse_action_str("x ≔ y + 1").unwrap();
        let ac = check_action(&a, &env);
        assert_eq!(ac.free_identifier.as_deref(), Some("y"));
    }

    #[test]
    fn action_check_flags_unknown_type_ascription_identifier() {
        let mut env = TypeEnv::new();
        env.insert("x", Type::Int);
        let a = parse_action_str("x ≔ card(∅ ⦂ ℙ(UNKNOWN))").unwrap();
        let ac = check_action(&a, &env);
        assert_eq!(ac.free_identifier.as_deref(), Some("UNKNOWN"));
    }

    #[test]
    fn action_check_binds_primed_becomes_such_that_targets() {
        let mut env = TypeEnv::new();
        env.insert("x", Type::Int);
        let a = parse_action_str("x :∣ x' = x").unwrap();
        let ac = check_action(&a, &env);
        assert_eq!(ac.free_identifier, None);
    }
}

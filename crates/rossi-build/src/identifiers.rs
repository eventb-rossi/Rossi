//! Declared-name validity that no project context can decide (EB033).
//!
//! Event-B spells the post-value of an assigned variable with a trailing
//! prime, so the prime belongs to a formula and never to a declaration.
//! Rodin enforces that in its static checker: `IdentifierModule` parses
//! every carrier set, constant, variable and event parameter with
//! `primeAllowed = false` and reports `InvalidIdentifierError` for a primed
//! one, dropping the name from the checked model. The single caller passing
//! `primeAllowed = true` is `MachineEventWitnessModule`, for a witness
//! *label*.
//!
//! The parser is deliberately not the place for it. `parser.rs`'s
//! `declared_name` gate is shared by three positions, and only one of them
//! may refuse a prime: an assignment target may already be primed (Rodin's
//! `MainParsers.makePrimedDecl` branches on `isPrimed()` precisely so `x' :∣
//! …` is not double-primed) and a quantifier binder may be (that is how the
//! model spells a such-that declaration). Rodin refuses a primed
//! declaration from an *SC module*, not from its parser or its database, so
//! checking it here is parity rather than compromise — and a Rodin
//! `.buc`/`.bum` that stores such a name still imports.
//!
//! The rule reads one name at a time, so — like [`crate::duplicates`] — it
//! has two views: this module reports the diagnostics for `rossi validate`'s
//! loose-text path, the LSP and the SC's up-front pass, while the SC's
//! per-component checks filter the offending names out of their output with
//! [`rossi::names::is_primed_identifier`] directly.
//!
//! A primed declaration being impossible is also what makes a *use* of a
//! primed name decidable without a project: no SEES / EXTENDS parent and no
//! abstract machine can ever put one in scope.

use rossi::Component;
use rossi::names::is_primed_identifier;

use crate::{Diagnostic, RuleId};

/// EB033 — one error per declared name carrying the after-state prime.
///
/// Only the identifier sites can be primed: a component or event name is a
/// `component_name`, whose grammar has no prime at all.
#[must_use]
pub fn component_primed_name_diagnostics(component: &Component) -> Vec<Diagnostic> {
    let mut diags = Vec::new();
    crate::lint::for_each_declared_name(component, |origin, kind, name, site, span| {
        if !site.is_math_identifier() || !is_primed_identifier(name) {
            return;
        }
        diags.push(Diagnostic {
            severity: RuleId::PrimedDeclaredName.default_severity(),
            origin: format!("{origin}.{name}"),
            message: format!(
                "{kind} `{name}` is declared with the after-state prime, which \
                 only a witness label may carry — rename it without the `'`"
            ),
            rule_id: Some(RuleId::PrimedDeclaredName),
            span,
        });
    });
    diags
}

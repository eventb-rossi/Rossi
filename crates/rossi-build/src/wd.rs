//! EB010 well-definedness diagnostics over the typed static-checker model.

use rossi::formula::{Assignment, Expression, Predicate, PredicateKind};
use rossi::pretty::PrettyPrinter;

use crate::sc_model::{EventDecl, ScModel};
use crate::{Diagnostic, Project, RuleId};

/// Emit one EB010 INFO diagnostic for every successfully checked formula with
/// a non-trivial well-definedness lemma.
pub fn run(project: &Project, model: &ScModel) -> Vec<Diagnostic> {
    let mut diagnostics = Vec::new();

    for component in &project.components {
        let name = component.component.name();
        match &component.component {
            rossi::Component::Context(_) => {
                let Some(context) = model.contexts.get(name) else {
                    continue;
                };
                for axiom in &context.record.axioms {
                    push_predicate(
                        &mut diagnostics,
                        format!("{name}.{}", axiom.label),
                        &axiom.typed,
                    );
                }
            }
            rossi::Component::Machine(_) => {
                let Some(machine) = model.machines.get(name) else {
                    continue;
                };
                for invariant in &machine.record.invariants {
                    push_predicate(
                        &mut diagnostics,
                        format!("{name}.{}", invariant.label),
                        &invariant.typed,
                    );
                }
                if let Some(variant) = &machine.record.variant
                    && let Some(typed) = &variant.typed
                {
                    let label = component
                        .rodin_ids
                        .last_variant_label()
                        .unwrap_or(variant.label);
                    push_expression(&mut diagnostics, format!("{name}.{label}"), typed);
                }
                for event in &machine.record.events {
                    push_event(&mut diagnostics, name, event);
                }
            }
        }
    }

    diagnostics
}

fn push_event(diagnostics: &mut Vec<Diagnostic>, machine: &str, event: &EventDecl) {
    let origin = |label: &str| format!("{machine}.{}/{label}", event.label);

    for guard in &event.guards {
        push_predicate(diagnostics, origin(&guard.label), &guard.typed);
    }
    for action in event.own_actions() {
        if let Some(typed) = &action.typed {
            push_assignment(diagnostics, origin(&action.label), typed);
        }
    }
    for witness in &event.witnesses {
        push_predicate(diagnostics, origin(&witness.label), &witness.typed);
    }
}

fn push_predicate(diagnostics: &mut Vec<Diagnostic>, origin: String, formula: &Predicate) {
    push_lemma(diagnostics, origin, formula.wd_lemma(), formula.span());
}

fn push_expression(diagnostics: &mut Vec<Diagnostic>, origin: String, formula: &Expression) {
    push_lemma(diagnostics, origin, formula.wd_lemma(), formula.span());
}

fn push_assignment(diagnostics: &mut Vec<Diagnostic>, origin: String, formula: &Assignment) {
    push_lemma(diagnostics, origin, formula.wd_lemma(), formula.span());
}

fn push_lemma(
    diagnostics: &mut Vec<Diagnostic>,
    origin: String,
    lemma: Predicate,
    span: Option<rossi::ast::Span>,
) {
    if matches!(
        lemma.kind(),
        PredicateKind::Literal(rossi::formula::tag::LiteralPredOp::BTrue)
    ) {
        return;
    }

    diagnostics.push(Diagnostic {
        severity: RuleId::WellDefinedness.default_severity(),
        origin,
        message: format!("Well-definedness condition: {}", render_lemma(&lemma)),
        rule_id: Some(RuleId::WellDefinedness),
        span,
    });
}

fn render_lemma(lemma: &Predicate) -> String {
    PrettyPrinter::rodin_formula_string().print_formula_predicate(lemma)
}

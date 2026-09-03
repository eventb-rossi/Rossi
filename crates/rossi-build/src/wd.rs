//! EB010 well-definedness diagnostics over the typed static-checker model.

use rossi::ast::{Located, SourceId, Span};
use rossi::formula::{Assignment, Expression, Predicate, PredicateKind};
use rossi::pretty::PrettyPrinter;

use crate::sc_model::{EventDecl, ScModel};
use crate::{Diagnostic, Project, ProjectComponent, RuleId};

/// One non-trivial well-definedness condition of a checked formula.
pub struct WdCondition {
    /// `"{component}.{label}"` for axioms, invariants, and variants;
    /// `"{component}.{event}/{label}"` for guards, actions, and witnesses —
    /// the same origin spelling the EB010 diagnostics use.
    pub origin: String,
    /// The type-checked WD lemma; never the trivial `⊤`.
    pub lemma: Predicate,
    /// Byte span of the source formula, with the component text it indexes
    /// (textual sources only).
    ///
    /// The source is carried because this walks a whole [`ScModel`]: a caller
    /// that passes several components gets conditions whose spans index
    /// different texts, and only the [`SourceId`] tells them apart.
    pub span: Option<Located<Span>>,
}

/// Collect the non-trivial well-definedness condition of every successfully
/// checked formula of `components`. [`run`] renders these as EB010
/// diagnostics; IDE tooling reads them structured (typically passing only the
/// components it annotates), so the two surfaces can never disagree.
pub fn conditions<'a>(
    components: impl IntoIterator<Item = &'a ProjectComponent>,
    model: &ScModel,
) -> Vec<WdCondition> {
    let mut conditions = Vec::new();

    for component in components {
        let source = component.source_id();
        let name = component.component.name();
        match &component.component {
            rossi::Component::Context(_) => {
                let Some(context) = model.contexts.get(name) else {
                    continue;
                };
                for axiom in &context.record.axioms {
                    push_predicate(
                        &mut conditions,
                        &source,
                        || format!("{name}.{}", axiom.label),
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
                        &mut conditions,
                        &source,
                        || format!("{name}.{}", invariant.label),
                        &invariant.typed,
                    );
                }
                for variant in &machine.record.variants {
                    if let Some(typed) = &variant.typed {
                        push_expression(
                            &mut conditions,
                            &source,
                            || format!("{name}.{}", variant.label),
                            typed,
                        );
                    }
                }
                for event in &machine.record.events {
                    push_event(&mut conditions, &source, name, event);
                }
            }
        }
    }

    conditions
}

/// Emit one EB010 INFO diagnostic for every successfully checked formula with
/// a non-trivial well-definedness lemma.
pub fn run(project: &Project, model: &ScModel) -> Vec<Diagnostic> {
    conditions(&project.components, model)
        .into_iter()
        .map(|condition| Diagnostic {
            severity: RuleId::WellDefinedness.default_severity(),
            origin: condition.origin,
            message: format!(
                "Well-definedness condition: {}",
                render_lemma(&condition.lemma)
            ),
            rule_id: Some(RuleId::WellDefinedness),
            // `origin` names the component, which is not the same as the
            // text the span indexes — `fold_project_diagnostic` in the CLI
            // has to drop the anchor when a name has several carriers.
            // Dropping the source here is deferred until `Diagnostic` itself
            // carries one, not a claim that it is redundant.
            span: condition.span.map(|located| located.value),
        })
        .collect()
}

fn push_event(
    conditions: &mut Vec<WdCondition>,
    source: &SourceId,
    machine: &str,
    event: &EventDecl,
) {
    let origin = |label: &str| format!("{machine}.{}/{label}", event.label);

    for guard in &event.guards {
        push_predicate(conditions, source, || origin(&guard.label), &guard.typed);
    }
    for action in event.own_actions() {
        if let Some(typed) = &action.typed {
            push_assignment(conditions, source, || origin(&action.label), typed);
        }
    }
    for witness in &event.witnesses {
        push_predicate(
            conditions,
            source,
            || origin(&witness.label),
            &witness.typed,
        );
    }
}

fn push_predicate(
    conditions: &mut Vec<WdCondition>,
    source: &SourceId,
    origin: impl FnOnce() -> String,
    formula: &Predicate,
) {
    push_lemma(
        conditions,
        source,
        origin,
        formula.wd_lemma(),
        formula.span(),
    );
}

fn push_expression(
    conditions: &mut Vec<WdCondition>,
    source: &SourceId,
    origin: impl FnOnce() -> String,
    formula: &Expression,
) {
    push_lemma(
        conditions,
        source,
        origin,
        formula.wd_lemma(),
        formula.span(),
    );
}

fn push_assignment(
    conditions: &mut Vec<WdCondition>,
    source: &SourceId,
    origin: impl FnOnce() -> String,
    formula: &Assignment,
) {
    push_lemma(
        conditions,
        source,
        origin,
        formula.wd_lemma(),
        formula.span(),
    );
}

fn push_lemma(
    conditions: &mut Vec<WdCondition>,
    source: &SourceId,
    origin: impl FnOnce() -> String,
    lemma: Predicate,
    span: Option<Span>,
) {
    if matches!(
        lemma.kind(),
        PredicateKind::Literal(rossi::formula::tag::LiteralPredOp::BTrue)
    ) {
        return;
    }

    // The origin is formatted only for surviving lemmas — the trivial (⊤)
    // majority returns above without allocating.
    conditions.push(WdCondition {
        origin: origin(),
        lemma,
        span: span.map(|span| Located::new(source.clone(), span)),
    });
}

fn render_lemma(lemma: &Predicate) -> String {
    PrettyPrinter::rodin_formula_string().print_formula_predicate(lemma)
}

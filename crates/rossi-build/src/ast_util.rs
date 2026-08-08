//! Small AST construction helpers shared across the static checker.

/// Names that an action writes to (its LHS targets). Shared by the SC
/// cascade-drop logic and the lint module's unmodified-variable / INIT
/// completeness checks.
pub(crate) fn lhs_variables(action: &rossi::Action) -> Vec<&str> {
    use rossi::{ActionKind, Ident};
    match &action.kind {
        ActionKind::Skip => Vec::new(),
        ActionKind::Assignment { assignments } => assignments
            .iter()
            .map(|(variable, _)| variable.as_str())
            .collect(),
        ActionKind::BecomesIn { variables, .. } | ActionKind::BecomesSuchThat { variables, .. } => {
            variables.iter().map(Ident::as_str).collect()
        }
    }
}

/// Source span of the named element called `name`, when present and located.
/// The static checker's type-inference passes work over the declared names, so
/// they use this to recover the offending constant / variable / parameter's
/// span and anchor a diagnostic on its declaration rather than the component.
pub(crate) fn named_element_span(
    elements: &[rossi::NamedElement],
    name: &str,
) -> Option<rossi::ast::Span> {
    elements
        .iter()
        .find(|e| e.name == name)
        .and_then(|e| e.span)
}

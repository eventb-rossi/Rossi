//! AST analysis and symbol extraction
//!
//! This module analyzes Event-B components and extracts symbols for navigation
//! and other LSP features.

use crate::identifier_utils::span_to_range;
use crate::lsp_types::{DocumentSymbol, Range, SymbolKind};
use rossi::ast::Span;
use rossi::{Component, Context, Event, EventStatus, Machine};

/// Extract document symbols from a component
pub fn extract_symbols(component: &Component, source: &str) -> Vec<DocumentSymbol> {
    match component {
        Component::Context(ctx) => extract_context_symbols(ctx, source),
        Component::Machine(machine) => extract_machine_symbols(machine, source),
    }
}

/// Extract symbols from a Context
fn extract_context_symbols(ctx: &Context, source: &str) -> Vec<DocumentSymbol> {
    let mut symbols = Vec::new();

    // Add SETS as enum symbols
    for set in &ctx.sets {
        symbols.push(create_symbol(
            set.name.clone(),
            SymbolKind::ENUM,
            "Set",
            name_range_or(set.span.as_ref(), default_range(), source),
        ));
    }

    // Add CONSTANTS as constant symbols
    for constant in &ctx.constants {
        symbols.push(create_symbol(
            constant.name.clone(),
            SymbolKind::CONSTANT,
            "Constant",
            name_range_or(constant.span.as_ref(), default_range(), source),
        ));
    }

    // Add AXIOMS (including theorems) as property symbols
    for axiom in &ctx.axioms {
        let label = axiom
            .label
            .clone()
            .unwrap_or_else(|| "unlabeled".to_string());
        let range = axiom
            .span
            .as_ref()
            .map_or_else(default_range, |span| span_to_range(span, source));
        let detail = if axiom.is_theorem { "Theorem" } else { "Axiom" };
        symbols.push(create_symbol(label, SymbolKind::PROPERTY, detail, range));
    }

    // Wrap in a parent symbol for the context
    let range = ctx
        .span
        .as_ref()
        .map_or_else(default_range, |span| span_to_range(span, source));
    let name_range = name_range_or(ctx.name_span.as_ref(), range, source);

    let context_symbol = DocumentSymbol {
        name: ctx.name.clone(),
        detail: Some("Context".to_string()),
        kind: SymbolKind::MODULE,
        tags: None,
        range,
        selection_range: name_range,
        children: Some(symbols),
        #[allow(deprecated)]
        deprecated: None,
    };

    vec![context_symbol]
}

/// Extract symbols from a Machine
fn extract_machine_symbols(machine: &Machine, source: &str) -> Vec<DocumentSymbol> {
    let mut symbols = Vec::new();

    // Add VARIABLES as variable symbols
    for var in &machine.variables {
        symbols.push(create_symbol(
            var.name.clone(),
            SymbolKind::VARIABLE,
            "Variable",
            name_range_or(var.span.as_ref(), default_range(), source),
        ));
    }

    // Add INVARIANTS (including theorems) as property symbols
    for invariant in &machine.invariants {
        let label = invariant
            .label
            .clone()
            .unwrap_or_else(|| "unlabeled".to_string());
        let range = invariant
            .span
            .as_ref()
            .map_or_else(default_range, |span| span_to_range(span, source));
        let detail = if invariant.is_theorem {
            "Theorem"
        } else {
            "Invariant"
        };
        symbols.push(create_symbol(label, SymbolKind::PROPERTY, detail, range));
    }

    // Add VARIANT if present
    if !machine.variants.is_empty() {
        symbols.push(create_symbol(
            "variant".to_string(),
            SymbolKind::NUMBER,
            "Variant",
            default_range(),
        ));
    }

    // Add INITIALISATION event if present
    if let Some(init) = &machine.initialisation {
        let mut init_children = Vec::new();

        // Add actions as nested symbols
        for action in &init.actions {
            let label = action
                .label
                .clone()
                .unwrap_or_else(|| "unlabeled".to_string());
            let range = action
                .span
                .as_ref()
                .map_or_else(default_range, |span| span_to_range(span, source));
            init_children.push(create_symbol(label, SymbolKind::PROPERTY, "Action", range));
        }

        // The whole event spans the outline row; the INITIALISATION name token
        // is its selection range, mirroring a regular event.
        let range = init
            .span
            .as_ref()
            .map_or_else(default_range, |span| span_to_range(span, source));
        let selection_range = name_range_or(init.name_span.as_ref(), range, source);

        let init_symbol = DocumentSymbol {
            name: "INITIALISATION".to_string(),
            detail: Some("Event".to_string()),
            kind: SymbolKind::CONSTRUCTOR,
            tags: None,
            range,
            selection_range,
            children: if init_children.is_empty() {
                None
            } else {
                Some(init_children)
            },
            #[allow(deprecated)]
            deprecated: None,
        };
        symbols.push(init_symbol);
    }

    // Add EVENTS as function symbols
    for event in &machine.events {
        symbols.push(extract_event_symbol(event, source));
    }

    // Wrap in a parent symbol for the machine
    let range = machine
        .span
        .as_ref()
        .map_or_else(default_range, |span| span_to_range(span, source));
    let name_range = name_range_or(machine.name_span.as_ref(), range, source);

    let machine_symbol = DocumentSymbol {
        name: machine.name.clone(),
        detail: Some("Machine".to_string()),
        kind: SymbolKind::MODULE,
        tags: None,
        range,
        selection_range: name_range,
        children: Some(symbols),
        #[allow(deprecated)]
        deprecated: None,
    };

    vec![machine_symbol]
}

/// Extract symbol from an Event
fn extract_event_symbol(event: &Event, source: &str) -> DocumentSymbol {
    let mut children = Vec::new();

    // Add parameters
    for param in &event.parameters {
        children.push(create_symbol(
            param.name.clone(),
            SymbolKind::TYPE_PARAMETER,
            "Parameter",
            name_range_or(param.span.as_ref(), default_range(), source),
        ));
    }

    // Add guards
    for guard in &event.guards {
        let label = guard
            .label
            .clone()
            .unwrap_or_else(|| "unlabeled".to_string());
        let range = guard
            .span
            .as_ref()
            .map_or_else(default_range, |span| span_to_range(span, source));
        children.push(create_symbol(label, SymbolKind::PROPERTY, "Guard", range));
    }

    // Add WITH bindings
    for lp in &event.with {
        let label = lp.label.clone().unwrap_or_else(|| "unlabeled".to_string());
        children.push(create_symbol(
            label,
            SymbolKind::PROPERTY,
            "With",
            name_range_or(lp.span.as_ref(), default_range(), source),
        ));
    }

    // Add witnesses
    for lp in &event.witnesses {
        let label = lp.label.clone().unwrap_or_else(|| "unlabeled".to_string());
        children.push(create_symbol(
            label,
            SymbolKind::PROPERTY,
            "Witness",
            name_range_or(lp.span.as_ref(), default_range(), source),
        ));
    }

    // Add actions
    for action in &event.actions {
        let label = action
            .label
            .clone()
            .unwrap_or_else(|| "unlabeled".to_string());
        let range = action
            .span
            .as_ref()
            .map_or_else(default_range, |span| span_to_range(span, source));
        children.push(create_symbol(label, SymbolKind::PROPERTY, "Action", range));
    }

    // Determine event detail based on status
    let detail = match event.status {
        Some(EventStatus::Ordinary) => "Event (ordinary)".to_string(),
        Some(EventStatus::Convergent) => "Event (convergent)".to_string(),
        Some(EventStatus::Anticipated) => "Event (anticipated)".to_string(),
        None => "Event".to_string(),
    };

    let range = event
        .span
        .as_ref()
        .map_or_else(default_range, |span| span_to_range(span, source));
    let name_range = name_range_or(event.name_span.as_ref(), range, source);

    DocumentSymbol {
        name: event.name.clone(),
        detail: Some(detail),
        kind: SymbolKind::FUNCTION,
        tags: None,
        range,
        selection_range: name_range,
        children: if children.is_empty() {
            None
        } else {
            Some(children)
        },
        #[allow(deprecated)]
        deprecated: None,
    }
}

/// Create a simple symbol
fn create_symbol(name: String, kind: SymbolKind, detail: &str, range: Range) -> DocumentSymbol {
    DocumentSymbol {
        name,
        detail: Some(detail.to_string()),
        kind,
        tags: None,
        range,
        selection_range: range,
        children: None,
        #[allow(deprecated)]
        deprecated: None,
    }
}

/// `name_span` as a range, or `fallback` when absent.
fn name_range_or(name_span: Option<&Span>, fallback: Range, source: &str) -> Range {
    name_span.map_or(fallback, |s| span_to_range(s, source))
}

/// Create a default range (0,0)-(0,0)
/// Used as fallback when span information is not available
pub(crate) fn default_range() -> Range {
    Range {
        start: crate::lsp_types::Position::new(0, 0),
        end: crate::lsp_types::Position::new(0, 0),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rossi::{LabeledPredicate, parse};

    #[test]
    fn test_extract_context_symbols() {
        let mut ctx = Context::new("test_ctx".to_string());
        ctx.sets = vec![
            rossi::NamedElement::new("SET1".to_string()),
            rossi::NamedElement::new("SET2".to_string()),
        ];
        ctx.constants = vec![
            rossi::NamedElement::new("const1".to_string()),
            rossi::NamedElement::new("const2".to_string()),
        ];
        ctx.axioms = vec![LabeledPredicate {
            label: Some("axm1".to_string()),
            is_theorem: false,
            predicate: rossi::parse_predicate_str("⊤").unwrap(),
            span: None,
            comment: None,
        }];

        let source = "";
        let symbols = extract_context_symbols(&ctx, source);

        assert_eq!(symbols.len(), 1); // One top-level context symbol
        let ctx_symbol = &symbols[0];
        assert_eq!(ctx_symbol.name, "test_ctx");
        assert_eq!(ctx_symbol.kind, SymbolKind::MODULE);

        let children = ctx_symbol.children.as_ref().unwrap();
        assert_eq!(children.len(), 5); // 2 sets + 2 constants + 1 axiom

        // Check sets
        assert_eq!(children[0].name, "SET1");
        assert_eq!(children[0].kind, SymbolKind::ENUM);
        assert_eq!(children[1].name, "SET2");
        assert_eq!(children[1].kind, SymbolKind::ENUM);

        // Check constants
        assert_eq!(children[2].name, "const1");
        assert_eq!(children[2].kind, SymbolKind::CONSTANT);
        assert_eq!(children[3].name, "const2");
        assert_eq!(children[3].kind, SymbolKind::CONSTANT);

        // Check axiom
        assert_eq!(children[4].name, "axm1");
        assert_eq!(children[4].kind, SymbolKind::PROPERTY);
    }

    #[test]
    fn test_extract_machine_symbols() {
        let mut machine = Machine::new("test_machine".to_string());
        machine.variables = vec![
            rossi::NamedElement::new("var1".to_string()),
            rossi::NamedElement::new("var2".to_string()),
        ];
        machine.invariants = vec![LabeledPredicate {
            label: Some("inv1".to_string()),
            is_theorem: false,
            predicate: rossi::parse_predicate_str("⊤").unwrap(),
            span: None,
            comment: None,
        }];

        let source = "";
        let symbols = extract_machine_symbols(&machine, source);

        assert_eq!(symbols.len(), 1); // One top-level machine symbol
        let machine_symbol = &symbols[0];
        assert_eq!(machine_symbol.name, "test_machine");
        assert_eq!(machine_symbol.kind, SymbolKind::MODULE);

        let children = machine_symbol.children.as_ref().unwrap();
        assert_eq!(children.len(), 3); // 2 variables + 1 invariant

        // Check variables
        assert_eq!(children[0].name, "var1");
        assert_eq!(children[0].kind, SymbolKind::VARIABLE);
        assert_eq!(children[1].name, "var2");
        assert_eq!(children[1].kind, SymbolKind::VARIABLE);

        // Check invariant
        assert_eq!(children[2].name, "inv1");
        assert_eq!(children[2].kind, SymbolKind::PROPERTY);
    }

    #[test]
    fn test_extract_symbols_from_parsed_context() {
        let source = r#"
        CONTEXT counter_ctx
        SETS
            STATUS
        CONSTANTS
            max_value
        AXIOMS
            @axm1 max_value = 100
        END
        "#;

        let component = parse(source).unwrap();
        let symbols = extract_symbols(&component, source);

        assert_eq!(symbols.len(), 1);
        let ctx_symbol = &symbols[0];
        assert_eq!(ctx_symbol.name, "counter_ctx");

        let children = ctx_symbol.children.as_ref().unwrap();
        assert!(children.iter().any(|s| s.name == "STATUS"));
        assert!(children.iter().any(|s| s.name == "max_value"));
        assert!(children.iter().any(|s| s.name == "axm1"));
    }

    #[test]
    fn test_extract_symbols_from_parsed_machine() {
        let source = r#"
        MACHINE counter
        VARIABLES
            count
        INVARIANTS
            @inv1 count >= 0
        EVENTS
            EVENT INITIALISATION
            THEN
                @act1 count := 0
            END

            EVENT increment
            WHERE
                @grd1 count < 100
            THEN
                @act1 count := count + 1
            END
        END
        "#;

        let component = parse(source).unwrap();
        let symbols = extract_symbols(&component, source);

        assert_eq!(symbols.len(), 1);
        let machine_symbol = &symbols[0];
        assert_eq!(machine_symbol.name, "counter");

        let children = machine_symbol.children.as_ref().unwrap();

        // Should have: count variable, inv1, INITIALISATION, increment event
        assert!(children.iter().any(|s| s.name == "count"));
        assert!(children.iter().any(|s| s.name == "inv1"));
        assert!(children.iter().any(|s| s.name == "INITIALISATION"));
        assert!(children.iter().any(|s| s.name == "increment"));

        // Check increment event has children
        let increment = children.iter().find(|s| s.name == "increment").unwrap();
        assert!(increment.children.is_some());
        let event_children = increment.children.as_ref().unwrap();
        assert!(event_children.iter().any(|s| s.name == "grd1"));
        assert!(event_children.iter().any(|s| s.name == "act1"));
    }

    #[test]
    fn initialisation_document_symbol_selects_the_name() {
        use crate::lsp_types::Position;

        // The INITIALISATION outline entry's selection range is the name token,
        // not the (0, 0) default it used to fall back to.
        let source = "MACHINE m\nVARIABLES\n    v\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 v := 0\n    END\nEND";
        let component = parse(source).unwrap();
        let symbols = extract_symbols(&component, source);
        let init = symbols[0]
            .children
            .as_ref()
            .unwrap()
            .iter()
            .find(|s| s.name == "INITIALISATION")
            .expect("INITIALISATION symbol present");

        // `    EVENT INITIALISATION`: the name begins at column 10 on line 4 and
        // runs the 14 columns of "INITIALISATION".
        assert_eq!(init.selection_range.start, Position::new(4, 10));
        assert_eq!(init.selection_range.end, Position::new(4, 24));
        // The full-event range is real, not the (0, 0) default.
        assert_ne!(init.range, default_range());
    }

    #[test]
    fn selection_range_contained_when_name_span_absent() {
        // An event whose name_span is None (e.g. the header was unreadable) must
        // still produce a DocumentSymbol where selectionRange ⊆ range.  The old
        // code fell back to (0,0)-(0,0) which lies outside any event not at the
        // very top of the file.
        let source = "MACHINE m\nVARIABLES\n    v\nEVENTS\n    EVENT step\n    END\nEND";
        let mut event = rossi::Event::new("step".to_string());
        // Place the span at the EVENT keyword on line 4 (byte 40 is an
        // approximation; what matters is that the range starts past line 0).
        event.span = Some(rossi::ast::Span { start: 40, end: 55 });
        event.name_span = None;

        let sym = extract_event_symbol(&event, source);

        // selectionRange.start must be ≥ range.start (line then column).
        let r = sym.range;
        let s = sym.selection_range;
        assert!(
            (s.start.line, s.start.character) >= (r.start.line, r.start.character)
                && (s.end.line, s.end.character) <= (r.end.line, r.end.character),
            "selection_range {s:?} must be contained in range {r:?}"
        );
    }

    #[test]
    fn test_event_status_in_detail() {
        let mut ordinary_event = Event::new("evt1".to_string());
        ordinary_event.status = Some(EventStatus::Ordinary);

        let mut convergent_event = Event::new("evt2".to_string());
        convergent_event.status = Some(EventStatus::Convergent);

        let mut anticipated_event = Event::new("evt3".to_string());
        anticipated_event.status = Some(EventStatus::Anticipated);

        let source = "";
        let sym1 = extract_event_symbol(&ordinary_event, source);
        assert_eq!(sym1.detail, Some("Event (ordinary)".to_string()));

        let sym2 = extract_event_symbol(&convergent_event, source);
        assert_eq!(sym2.detail, Some("Event (convergent)".to_string()));

        let sym3 = extract_event_symbol(&anticipated_event, source);
        assert_eq!(sym3.detail, Some("Event (anticipated)".to_string()));
    }

    #[test]
    fn document_symbol_detail_vocabulary_is_stable() {
        // `detail` is how an editor outline and any third-party integrator tell
        // one Event-B construct from another, so these strings are a contract:
        // the table in the crate README must keep matching them. The three
        // status-qualified event forms are pinned by
        // `test_event_status_in_detail`; everything else is pinned here.
        fn flatten(symbols: &[DocumentSymbol], out: &mut Vec<(SymbolKind, String)>) {
            for symbol in symbols {
                out.push((symbol.kind, symbol.detail.clone().expect("detail set")));
                flatten(symbol.children.as_deref().unwrap_or(&[]), out);
            }
        }

        let vocabulary = |source: &str| {
            let component = parse(source).unwrap();
            let mut out = Vec::new();
            flatten(&extract_symbols(&component, source), &mut out);
            out
        };

        let context_source = r#"
        CONTEXT c
        SETS
            S
        CONSTANTS
            k
        AXIOMS
            @axm1 k ∈ S
            theorem @thm1 ⊤
        END
        "#;
        assert_eq!(
            vocabulary(context_source),
            vec![
                (SymbolKind::MODULE, "Context".to_string()),
                (SymbolKind::ENUM, "Set".to_string()),
                (SymbolKind::CONSTANT, "Constant".to_string()),
                (SymbolKind::PROPERTY, "Axiom".to_string()),
                (SymbolKind::PROPERTY, "Theorem".to_string()),
            ]
        );

        let machine_source = r#"
        MACHINE m
        VARIABLES
            v
        INVARIANTS
            @inv1 v ∈ ℕ
            theorem @thm1 ⊤
        VARIANT
            v
        EVENTS
            EVENT INITIALISATION
            THEN
                @act1 v := 0
            END

            EVENT step
            ANY p
            WHERE
                @grd1 p ∈ ℕ
            WITH
                @wth1 ⊤
            WITNESS
                @wit1 ⊤
            THEN
                @act1 v := p
            END
        END
        "#;
        assert_eq!(
            vocabulary(machine_source),
            vec![
                (SymbolKind::MODULE, "Machine".to_string()),
                (SymbolKind::VARIABLE, "Variable".to_string()),
                (SymbolKind::PROPERTY, "Invariant".to_string()),
                (SymbolKind::PROPERTY, "Theorem".to_string()),
                (SymbolKind::NUMBER, "Variant".to_string()),
                // INITIALISATION is a CONSTRUCTOR carrying the bare "Event",
                // while a status-less regular event is a FUNCTION carrying the
                // same string: the kind is what separates them.
                (SymbolKind::CONSTRUCTOR, "Event".to_string()),
                (SymbolKind::PROPERTY, "Action".to_string()),
                (SymbolKind::FUNCTION, "Event".to_string()),
                (SymbolKind::TYPE_PARAMETER, "Parameter".to_string()),
                (SymbolKind::PROPERTY, "Guard".to_string()),
                (SymbolKind::PROPERTY, "With".to_string()),
                (SymbolKind::PROPERTY, "Witness".to_string()),
                (SymbolKind::PROPERTY, "Action".to_string()),
            ]
        );
    }

    #[test]
    fn declaration_symbols_point_at_their_declaration() {
        use crate::lsp_types::Position;

        // Sets, constants, variables and WITH / WITNESS predicates used to
        // report the (0, 0) default even though the parser records a span for
        // each, so jumping to one from the outline landed at the top of the
        // file instead of on the declaration.
        let context_source =
            "CONTEXT c\nSETS\n    S\nCONSTANTS\n    k\nAXIOMS\n    @axm1 k ∈ S\nEND";
        let component = parse(context_source).unwrap();
        let symbols = extract_symbols(&component, context_source);
        let children = symbols[0].children.as_ref().unwrap();

        assert_eq!(children[0].name, "S");
        assert_eq!(children[0].range.start, Position::new(2, 4));
        assert_eq!(children[1].name, "k");
        assert_eq!(children[1].range.start, Position::new(4, 4));

        let machine_source = "MACHINE m\nVARIABLES\n    v\nEVENTS\n    EVENT step\n    WITH\n        @wth1 ⊤\n    WITNESS\n        @wit1 ⊤\n    THEN\n        @act1 v := 0\n    END\nEND";
        let component = parse(machine_source).unwrap();
        let symbols = extract_symbols(&component, machine_source);
        let children = symbols[0].children.as_ref().unwrap();

        assert_eq!(children[0].name, "v");
        assert_eq!(children[0].range.start, Position::new(2, 4));

        let event = children.iter().find(|s| s.name == "step").unwrap();
        let event_children = event.children.as_ref().unwrap();
        let with = event_children.iter().find(|s| s.name == "wth1").unwrap();
        assert_eq!(with.range.start, Position::new(6, 8));
        let witness = event_children.iter().find(|s| s.name == "wit1").unwrap();
        assert_eq!(witness.range.start, Position::new(8, 8));
    }
}

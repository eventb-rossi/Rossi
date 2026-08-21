//! Inlay hints: inferred declaration types rendered after each declared name.
//!
//! Event-B declarations are bare identifiers — `VARIABLES x`, `CONSTANTS c`,
//! `ANY p` — whose types are recovered by the static checker from invariants,
//! axioms, and guards, often clauses away or up the REFINES/EXTENDS chain.
//! This provider surfaces the inferred type at the declaration site itself.
//!
//! Unlike the diagnostics path, which deliberately avoids type inference on
//! every keystroke, hints are pull-based: the editor asks for the visible
//! range when it needs them, the whole-document hint list is computed once
//! over the document's dependency closure, and repeated requests at an
//! unchanged buffer state are served from a per-URI cache.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use rossi::Component;
use rossi::ast::NamedElement;
use rossi::deps::kind_and_name;
use rossi::formula::{FormulaFactory, Type};

use crate::component_loader::ComponentLoader;
use crate::config::{FormatConfig, RossiConfig};
use crate::cross_references::CrossReferenceManager;
use crate::document::DocumentManager;
use crate::lsp_types::{InlayHint, InlayHintKind, InlayHintLabel, InlayHintTooltip, Range, Url};
use crate::position::PositionIndex;
use crate::resolved_environment::ResolvedEnvironments;

/// Serves `textDocument/inlayHint` from per-URI cached whole-document lists.
pub struct InlayHintsProvider {
    document_manager: Arc<DocumentManager>,
    cross_reference_manager: Arc<CrossReferenceManager>,
    cache: parking_lot::Mutex<HashMap<Url, CachedHints>>,
}

/// One cached whole-document hint computation. Valid while no buffer anywhere
/// has changed (the closure's inputs are open buffers plus disk fallbacks, so
/// any open/change is the moment inferred types can change) and the request
/// still runs under the same configuration snapshot.
struct CachedHints {
    change_counter: u64,
    /// Compared by `Arc::ptr_eq`: the config manager swaps the whole `Arc` on
    /// every update, so pointer identity is exactly "unchanged since".
    config: Arc<RossiConfig>,
    /// In document order, un-clipped; requests filter by their range.
    hints: Arc<Vec<InlayHint>>,
}

impl InlayHintsProvider {
    pub fn new(
        document_manager: Arc<DocumentManager>,
        cross_reference_manager: Arc<CrossReferenceManager>,
    ) -> Self {
        Self {
            document_manager,
            cross_reference_manager,
            cache: parking_lot::Mutex::new(HashMap::new()),
        }
    }

    /// The hints for `uri` clipped to `range`; `None` when the document is not
    /// open. A cache hit is a lock plus a filter; a miss runs the static check
    /// over the document's dependency closure. Concurrent misses for one URI
    /// may compute twice — clients debounce their requests, so a rare
    /// duplicate is preferred over another lock order to reason about.
    pub fn inlay_hints(
        &self,
        uri: &Url,
        range: Range,
        config: &Arc<RossiConfig>,
    ) -> Option<Vec<InlayHint>> {
        // Read the stamp before computing: an edit landing mid-compute then
        // invalidates the entry we store, never the other way around.
        let change_counter = self.document_manager.change_counter();
        {
            let cache = self.cache.lock();
            if let Some(entry) = cache.get(uri)
                && entry.change_counter == change_counter
                && Arc::ptr_eq(&entry.config, config)
            {
                return Some(clip(&entry.hints, range));
            }
        }

        let hints = Arc::new(self.compute(uri, config)?);
        self.cache.lock().insert(
            uri.clone(),
            CachedHints {
                change_counter,
                config: Arc::clone(config),
                hints: Arc::clone(&hints),
            },
        );
        Some(clip(&hints, range))
    }

    /// Drop the cached hints of a closed document.
    pub fn evict(&self, uri: &Url) {
        self.cache.lock().remove(uri);
    }

    /// Compute the whole-document hint list: assemble the dependency closure
    /// from current buffer snapshots, run the static check (without proof
    /// obligations), and join the typed declaration records back to this
    /// file's AST declaration sites, which carry the spans.
    fn compute(&self, uri: &Url, config: &RossiConfig) -> Option<Vec<InlayHint>> {
        let doc = self.document_manager.parse_result(uri)?;

        // The loadable closure of every component in this file, the roots
        // first. Dedup by kind and name: a merged file's machine may SEES a
        // context sitting right next to it.
        let loader =
            ComponentLoader::new(&self.cross_reference_manager, Some(&self.document_manager));
        let mut environments = ResolvedEnvironments::new();
        let mut seen = HashSet::new();
        let mut components = Vec::new();
        for component in doc.components() {
            if seen.insert(kind_and_name(component)) {
                components.push(component.clone());
            }
        }
        for component in doc.components() {
            let environment = environments.resolve(component, &loader);
            for dependency in environment
                .refined_machines()
                .into_iter()
                .chain(environment.visible_contexts())
                .chain(environment.extended_contexts())
            {
                if seen.insert(kind_and_name(dependency)) {
                    components.push(dependency.clone());
                }
            }
        }

        // Spans stay resolvable against `doc.text()`; the project needs no
        // `source` of its own. Dependencies imported from Rodin XML carry no
        // spans, but only this file's declaration sites are read below.
        let project = rossi_build::Project::new(
            "lsp-inlay-hints",
            components
                .into_iter()
                .map(|component| rossi_build::ProjectComponent {
                    filename: format!("{}.eventb", component.name()),
                    component,
                    rodin_ids: rossi_build::rodin_ids::RodinIds::default(),
                    source: None,
                })
                .collect(),
        );
        // Drop-but-continue: whatever failed to check is simply absent from
        // the model, and its declarations get no hints.
        let (_result, model) = rossi_build::check_with_model(&project);

        let index = PositionIndex::new(doc.text());
        let mut hints = Vec::new();
        for component in doc.components() {
            match component {
                Component::Machine(machine) => {
                    let Some(checked) = model.machines.get(&machine.name) else {
                        continue;
                    };
                    let types: HashMap<&str, &Type> = checked
                        .record
                        .variables
                        .iter()
                        .map(|variable| (variable.name.as_str(), &variable.ty))
                        .collect();
                    push_declaration_hints(&mut hints, &machine.variables, &types, &index, config);

                    let events: HashMap<&str, _> = checked
                        .record
                        .events
                        .iter()
                        .map(|event| (event.label.as_str(), event))
                        .collect();
                    for event in &machine.events {
                        let Some(decl) = events.get(event.name.as_str()) else {
                            continue;
                        };
                        let types: HashMap<&str, &Type> = decl
                            .parameters
                            .iter()
                            .map(|parameter| (parameter.name.as_str(), &parameter.ty))
                            .collect();
                        push_declaration_hints(
                            &mut hints,
                            &event.parameters,
                            &types,
                            &index,
                            config,
                        );
                    }
                }
                Component::Context(context) => {
                    let Some(checked) = model.contexts.get(&context.name) else {
                        continue;
                    };
                    let types: HashMap<&str, &Type> = checked
                        .record
                        .constants
                        .iter()
                        .map(|constant| (constant.name.as_str(), &constant.ty))
                        .collect();
                    push_declaration_hints(&mut hints, &context.constants, &types, &index, config);
                    // Carrier sets are deliberately not hinted: a set S always
                    // types as ℙ(S), so the hint would carry no information.
                }
            }
        }
        hints.sort_by_key(|hint| hint.position);
        Some(hints)
    }
}

/// Append one `: τ` hint per declared name that the checker typed and the
/// textual parser located. Names without a span (Rodin-XML imports) or
/// without an inferred type (no typing predicate found) are skipped.
fn push_declaration_hints(
    hints: &mut Vec<InlayHint>,
    declarations: &[NamedElement],
    types: &HashMap<&str, &Type>,
    index: &PositionIndex,
    config: &RossiConfig,
) {
    for declaration in declarations {
        let Some(span) = &declaration.span else {
            continue;
        };
        let Some(ty) = types.get(declaration.name.as_str()) else {
            continue;
        };
        let rendered = render_type(ty, &config.format);
        let max_length = config.inlay_hints.max_length as usize;
        let (label, tooltip) = if max_length > 0 && rendered.chars().count() > max_length {
            let truncated: String = rendered
                .chars()
                .take(max_length.saturating_sub(1))
                .collect();
            (
                format!(": {truncated}…"),
                Some(InlayHintTooltip::String(rendered)),
            )
        } else {
            (format!(": {rendered}"), None)
        };
        hints.push(InlayHint {
            position: index.position(span.end),
            label: InlayHintLabel::String(label),
            kind: Some(InlayHintKind::TYPE),
            text_edits: None,
            tooltip,
            padding_left: None,
            padding_right: None,
            data: None,
        });
    }
}

/// Render a type in the user's configured formatting style. The canonical
/// Rodin spelling is Unicode; the ASCII spelling goes through the shared
/// style-resolved printer so operator spellings match formatted output.
/// Parametric types have no expression form yet and always render canonically.
fn render_type(ty: &Type, format: &FormatConfig) -> String {
    if format.use_unicode || contains_parametric(ty) {
        return ty.to_rodin_canonical();
    }
    let mut printer = format.printer();
    printer.max_line_width = 0;
    printer.print_formula_expression(&ty.to_expression(&FormulaFactory::default_factory()))
}

fn contains_parametric(ty: &Type) -> bool {
    match ty {
        Type::Bool | Type::Int | Type::Given(_) => false,
        Type::Pow(inner) => contains_parametric(inner),
        Type::Prod(left, right) => contains_parametric(left) || contains_parametric(right),
        Type::Parametric { .. } => true,
    }
}

fn clip(hints: &[InlayHint], range: Range) -> Vec<InlayHint> {
    hints
        .iter()
        .filter(|hint| hint.position >= range.start && hint.position <= range.end)
        .cloned()
        .collect()
}

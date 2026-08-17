//! The findings overlay: animate results stored per `(machine, mode)` and
//! re-anchored onto the live buffers every time diagnostics are published.
//!
//! Findings survive edits the way the proof-status overlay does: they are
//! keyed by label/event *name*, not by position, and each publish resolves
//! them against the current parse — an anchor that no longer resolves falls
//! back to the machine header rather than disappearing. A new run of the
//! same `(machine, mode)` replaces its slot wholesale; a clean verdict
//! replaces it with nothing, which retracts the stale diagnostics.

use std::collections::HashMap;

use crate::document::ParsedDocument;
use crate::lsp_types::*;
use crate::position::span_to_range;

use super::AnimateMode;
use super::closure::Closure;
use super::report::{PoResult, Verdict};

/// The `source` every animate diagnostic carries. Deliberately distinct from
/// the `"rossi"` source the rest of the server publishes: these findings
/// come from an external tool the user installs and configures separately,
/// and the distinct source lets clients filter or style them as such.
pub(crate) const SOURCE: &str = "eventb-animate";

/// One result of a run, anchored by name and resolved at publish time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Finding {
    /// The file that declared the anchored element when the run started.
    pub uri: Url,
    /// The component the anchor lives in.
    pub component: String,
    pub anchor: Anchor,
    /// Diagnostic code: `animate-inv`, `animate-deadlock`, `animate-finding`,
    /// or `animate-po`.
    pub code: &'static str,
    pub message: String,
}

/// Where a finding lands in its component, from most to least specific.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Anchor {
    /// The `@label` line of the named invariant.
    InvariantLabel(String),
    /// The named event — on the named guard/action label inside it when one
    /// resolves, else on the event name. `INITIALISATION` is addressable.
    Event {
        event: String,
        label: Option<String>,
    },
    /// The component's name token (or `MACHINE` header line mid-edit).
    MachineHeader,
    /// The clicked machine's `INVARIANTS` section header.
    InvariantsSection,
}

/// All stored findings, keyed by `(machine, mode)` so the two lens flows
/// retract independently.
#[derive(Default)]
pub struct FindingsOverlay {
    findings: HashMap<(String, AnimateMode), Vec<Finding>>,
}

impl FindingsOverlay {
    /// Replace one `(machine, mode)` slot. Returns whether anything visible
    /// changed (callers republish only then). An empty `findings` removes
    /// the slot — the retraction path.
    pub(crate) fn apply(
        &mut self,
        machine: String,
        mode: AnimateMode,
        findings: Vec<Finding>,
    ) -> bool {
        let key = (machine, mode);
        if findings.is_empty() {
            return self.findings.remove(&key).is_some();
        }
        if self.findings.get(&key) == Some(&findings) {
            return false;
        }
        self.findings.insert(key, findings);
        true
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.findings.is_empty()
    }
}

/// The overlay's diagnostics for one document: every stored finding whose
/// run-time file is `uri`, re-anchored against the current parse. Like the
/// proof-status overlay, this is not gated on a clean parse — the text-scan
/// fallbacks keep the anchors meaningful mid-edit.
pub(crate) fn animate_diagnostics(
    uri: &Url,
    doc: &ParsedDocument,
    overlay: &FindingsOverlay,
) -> Vec<Diagnostic> {
    if overlay.is_empty() {
        return Vec::new();
    }
    let mut diagnostics = Vec::new();
    for findings in overlay.findings.values() {
        for finding in findings.iter().filter(|f| f.uri == *uri) {
            diagnostics.push(Diagnostic {
                range: resolve_anchor(doc, &finding.component, &finding.anchor),
                severity: Some(DiagnosticSeverity::ERROR),
                code: Some(NumberOrString::String(finding.code.to_string())),
                source: Some(SOURCE.to_string()),
                message: finding.message.clone(),
                ..Diagnostic::default()
            });
        }
    }
    diagnostics
}

fn resolve_anchor(doc: &ParsedDocument, component: &str, anchor: &Anchor) -> Range {
    let text = doc.text();
    let machine = doc.components().iter().find_map(|c| match c {
        rossi::Component::Machine(m) if m.name == component => Some(m),
        _ => None,
    });
    match anchor {
        Anchor::MachineHeader => header_range(doc, text, component),
        Anchor::InvariantLabel(label) => {
            if let Some(machine) = machine
                && let Some(span) = machine
                    .invariants
                    .iter()
                    .find(|inv| inv.label.as_deref() == Some(label))
                    .and_then(|inv| inv.span)
            {
                return span_to_range(&span, text);
            }
            let window = component_window(doc, text, component);
            find_label_line(text, window, label)
                .map(|(line, raw)| crate::position::full_line_range(raw, line as u32))
                .unwrap_or_else(|| header_range(doc, text, component))
        }
        Anchor::Event { event, label } => {
            if let Some(machine) = machine
                && let Some(span) = event_span(machine, event, label.as_deref())
            {
                return span_to_range(&span, text);
            }
            header_range(doc, text, component)
        }
        Anchor::InvariantsSection => {
            let window = component_window(doc, text, component);
            crate::component_util::lines_in_window(text, window)
                .find(|(_, line)| {
                    crate::text_utils::line_keyword_is(line, rossi::keywords::KeywordId::Invariants)
                })
                .map(|(line, raw)| crate::position::full_line_range(raw, line as u32))
                .unwrap_or_else(|| header_range(doc, text, component))
        }
    }
}

/// The inclusive line window bounding `component`'s text — the parsed span
/// when available, else the header-scan region (header line to the next
/// header), else the whole document. Bounds the text-scan fallbacks so a
/// finding never anchors inside a *different* component of the same file.
fn component_window(doc: &ParsedDocument, text: &str, component: &str) -> (usize, usize) {
    if let Some(parsed) = doc.components().iter().find(|c| c.name() == component) {
        return crate::component_util::component_line_window(parsed, text);
    }
    let mut rest = crate::text_utils::header_lines(text).skip_while(|h| h.name != Some(component));
    match rest.next() {
        Some(header) => (
            header.line,
            rest.next().map_or(usize::MAX, |next| next.line - 1),
        ),
        None => (0, usize::MAX),
    }
}

/// The named event's most specific span: the named guard/action label inside
/// it when one resolves, else the event's name token.
fn event_span(
    machine: &rossi::Machine,
    event: &str,
    label: Option<&str>,
) -> Option<rossi::ast::Span> {
    if event == "INITIALISATION" {
        let init = machine.initialisation.as_ref()?;
        if let Some(label) = label {
            let labeled = init
                .actions
                .iter()
                .find(|a| a.label.as_deref() == Some(label))
                .and_then(|a| a.span)
                .or_else(|| {
                    init.with
                        .iter()
                        .chain(&init.witnesses)
                        .find(|p| p.label.as_deref() == Some(label))
                        .and_then(|p| p.span)
                });
            if labeled.is_some() {
                return labeled;
            }
        }
        return init.name_span.or(init.span);
    }
    let found = machine.events.iter().find(|e| e.name == event)?;
    if let Some(label) = label {
        let labeled = found
            .guards
            .iter()
            .chain(&found.with)
            .chain(&found.witnesses)
            .find(|p| p.label.as_deref() == Some(label))
            .and_then(|p| p.span)
            .or_else(|| {
                found
                    .actions
                    .iter()
                    .find(|a| a.label.as_deref() == Some(label))
                    .and_then(|a| a.span)
            });
        if labeled.is_some() {
            return labeled;
        }
    }
    found.name_span.or(found.span)
}

/// The component's name-token range, with a header text scan as the mid-edit
/// fallback: the header line *naming* `component` when one exists, else the
/// first `MACHINE`/`CONTEXT` header, else the document start. A multi-machine
/// file mid-edit must not pin another machine's finding on the first header.
fn header_range(doc: &ParsedDocument, text: &str, component: &str) -> Range {
    if let Some(span) = doc
        .components()
        .iter()
        .find(|c| c.name() == component)
        .and_then(|c| c.name_span().or_else(|| c.span()))
    {
        return span_to_range(&span, text);
    }
    let mut first_header = None;
    for header in crate::text_utils::header_lines(text) {
        if header.name == Some(component) {
            return crate::position::full_line_range(header.text, header.line as u32);
        }
        first_header.get_or_insert((header.line, header.text));
    }
    let (line, raw) = first_header.unwrap_or((0, text.lines().next().unwrap_or("")));
    crate::position::full_line_range(raw, line as u32)
}

/// Find the line declaring `@label` within an inclusive line window (exact
/// label match; handles the `theorem @label predicate` ordering the grammar
/// also accepts).
fn find_label_line<'t>(
    text: &'t str,
    window: (usize, usize),
    label: &str,
) -> Option<(usize, &'t str)> {
    crate::component_util::lines_in_window(text, window).find(|(_, line)| {
        let trimmed = line.trim_start();
        let trimmed = trimmed
            .strip_prefix("theorem")
            .map(str::trim_start)
            .unwrap_or(trimmed);
        trimmed.strip_prefix('@').is_some_and(|rest| {
            rest.strip_prefix(label).is_some_and(|after| {
                !after
                    .chars()
                    .next()
                    .is_some_and(crate::text_utils::is_identifier_char)
            })
        })
    })
}

fn state_suffix(state: &str) -> String {
    if state.trim().is_empty() {
        String::new()
    } else {
        format!(
            " (state: {})",
            state.split_whitespace().collect::<Vec<_>>().join(" ")
        )
    }
}

/// The findings a verdict produces, total over [`Verdict`] so the two lens
/// flows cannot disagree about which verdicts yield diagnostics. Only
/// violations and disproofs yield any; clean, inconclusive, and error
/// verdicts return an empty set, which retracts the previous run's.
pub(crate) fn findings(verdict: &Verdict, closure: &Closure) -> Vec<Finding> {
    match verdict {
        Verdict::PoDisproved { disproved, .. } => po_findings(disproved, closure),
        Verdict::InvariantViolation {
            violated, state, ..
        } => {
            let (matched, unmatched) =
                super::report::match_violated(violated, &closure.invariants, &closure.machine);
            let mut findings: Vec<Finding> = matched
                .into_iter()
                .map(|info| Finding {
                    uri: info.uri.clone(),
                    component: info.component.clone(),
                    anchor: Anchor::InvariantLabel(info.label.clone()),
                    code: "animate-inv",
                    message: format!(
                        "Invariant @{} violated during model check of {}{}",
                        info.label,
                        closure.machine,
                        state_suffix(state)
                    ),
                })
                .collect();
            if !unmatched.is_empty() || findings.is_empty() {
                let detail = if unmatched.is_empty() {
                    String::new()
                } else {
                    format!(" — violated: {}", unmatched.join("; "))
                };
                findings.push(Finding {
                    uri: closure.uri.clone(),
                    component: closure.machine.clone(),
                    anchor: Anchor::InvariantsSection,
                    code: "animate-inv",
                    message: format!(
                        "Invariant violation during model check of {}{}{}",
                        closure.machine,
                        state_suffix(state),
                        detail
                    ),
                });
            }
            findings
        }
        Verdict::Deadlock { state, steps } => vec![Finding {
            uri: closure.uri.clone(),
            component: closure.machine.clone(),
            anchor: Anchor::MachineHeader,
            code: "animate-deadlock",
            message: format!(
                "Deadlock: no event of {} is enabled after {steps} step(s){}",
                closure.machine,
                state_suffix(state)
            ),
        }],
        Verdict::OtherFinding { category, message } => vec![Finding {
            uri: closure.uri.clone(),
            component: closure.machine.clone(),
            anchor: Anchor::MachineHeader,
            code: "animate-finding",
            message: format!(
                "Model check of {} found {category}: {message}",
                closure.machine
            ),
        }],
        _ => Vec::new(),
    }
}

/// The findings for the disproved subset of a po run. Each PO name
/// (`component/…/TYPE`) anchors on the named invariant when one of its
/// middle segments is an invariant label of that component, else on the
/// named event (with the sibling segment as the guard/action label), else on
/// the component header.
fn po_findings(disproved: &[PoResult], closure: &Closure) -> Vec<Finding> {
    disproved
        .iter()
        .map(|po| {
            let (uri, component, anchor) = resolve_po_anchor(&po.name, closure);
            Finding {
                uri,
                component,
                anchor,
                code: "animate-po",
                message: format!("PO {} disproved by ProB: {}", po.name, po.message),
            }
        })
        .collect()
}

fn resolve_po_anchor(name: &str, closure: &Closure) -> (Url, String, Anchor) {
    let fallback = || {
        (
            closure.uri.clone(),
            closure.machine.clone(),
            Anchor::MachineHeader,
        )
    };
    let segments: Vec<&str> = name.split('/').collect();
    if segments.len() < 2 {
        return fallback();
    }
    let Some(info) = closure.infos.iter().find(|i| i.name == segments[0]) else {
        return fallback();
    };
    let middle = &segments[1..segments.len() - 1];
    if let Some(label) = middle.iter().find(|s| {
        closure
            .invariants
            .iter()
            .any(|inv| inv.component == info.name && inv.label == **s)
    }) {
        return (
            info.uri.clone(),
            info.name.clone(),
            Anchor::InvariantLabel((*label).to_string()),
        );
    }
    if let Some(event) = middle.iter().find(|s| info.event_names.contains(**s)) {
        let label = middle
            .iter()
            .find(|s| s != &event)
            .map(|s| (*s).to_string());
        return (
            info.uri.clone(),
            info.name.clone(),
            Anchor::Event {
                event: (*event).to_string(),
                label,
            },
        );
    }
    (info.uri.clone(), info.name.clone(), Anchor::MachineHeader)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    use super::super::closure::{ComponentInfo, InvariantInfo};

    const MACHINE: &str = "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x ∈ ℕ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 x := 0\n    END\n\n    EVENT inc\n    WHERE\n        @grd1 x < 10\n    THEN\n        @act1 x := x + 1\n    END\nEND\n";

    fn parsed() -> ParsedDocument {
        ParsedDocument::from_text(MACHINE.to_string())
    }

    fn test_closure() -> Closure {
        let uri = Url::parse("file:///m.eventb").unwrap();
        Closure {
            machine: "m".to_string(),
            uri: uri.clone(),
            components: Vec::new(),
            invariants: vec![InvariantInfo {
                label: "inv1".to_string(),
                component: "m".to_string(),
                uri: uri.clone(),
                renderings: vec!["x∈ℕ".to_string(), "x:NAT".to_string()],
            }],
            infos: vec![ComponentInfo {
                name: "m".to_string(),
                uri,
                event_names: HashSet::from(["INITIALISATION".to_string(), "inc".to_string()]),
            }],
        }
    }

    fn published(findings: Vec<Finding>) -> Vec<Diagnostic> {
        let mut overlay = FindingsOverlay::default();
        overlay.apply("m".to_string(), AnimateMode::Check, findings);
        animate_diagnostics(
            &Url::parse("file:///m.eventb").unwrap(),
            &parsed(),
            &overlay,
        )
    }

    fn line_of(needle: &str) -> u32 {
        MACHINE
            .lines()
            .position(|line| line.contains(needle))
            .unwrap() as u32
    }

    #[test]
    fn violation_anchors_on_the_label_line_of_the_declaring_machine() {
        let verdict = Verdict::InvariantViolation {
            violated: vec!["x : NAT".to_string()],
            state: "x = -1".to_string(),
            steps: 2,
        };
        let findings = findings(&verdict, &test_closure());
        assert_eq!(findings.len(), 1);
        let diags = published(findings);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].range.start.line, line_of("@inv1"));
        assert_eq!(diags[0].source.as_deref(), Some("eventb-animate"));
        assert_eq!(
            diags[0].code,
            Some(NumberOrString::String("animate-inv".to_string()))
        );
        assert!(diags[0].message.contains("@inv1"), "{}", diags[0].message);
    }

    #[test]
    fn unmatched_predicates_fall_back_to_the_invariants_section() {
        let verdict = Verdict::InvariantViolation {
            violated: vec!["y = 0".to_string()],
            state: String::new(),
            steps: 1,
        };
        let findings = findings(&verdict, &test_closure());
        assert_eq!(findings.len(), 1);
        assert_eq!(findings[0].anchor, Anchor::InvariantsSection);
        let diags = published(findings);
        assert_eq!(diags[0].range.start.line, line_of("INVARIANTS"));
        assert!(diags[0].message.contains("y = 0"), "{}", diags[0].message);
    }

    #[test]
    fn deadlock_anchors_on_the_machine_header() {
        let verdict = Verdict::Deadlock {
            state: "x = 10".to_string(),
            steps: 10,
        };
        let findings = findings(&verdict, &test_closure());
        assert_eq!(findings[0].code, "animate-deadlock");
        let diags = published(findings);
        assert_eq!(diags[0].range.start.line, 0);
        // The parsed anchor is the name token, not column zero.
        assert_eq!(diags[0].range.start.character, 8);
    }

    #[test]
    fn po_names_resolve_invariant_then_event_then_header() {
        let closure = test_closure();
        let po = |name: &str| PoResult {
            name: name.to_string(),
            message: "disproved".to_string(),
        };

        // An invariant label among the middle segments wins.
        let findings = po_findings(&[po("m/INITIALISATION/inv1/INV")], &closure);
        assert_eq!(
            findings[0].anchor,
            Anchor::InvariantLabel("inv1".to_string())
        );
        assert_eq!(published(findings)[0].range.start.line, line_of("@inv1"));

        // Otherwise a known event name, with the sibling segment as label.
        let findings = po_findings(&[po("m/inc/grd1/GRD")], &closure);
        assert_eq!(
            findings[0].anchor,
            Anchor::Event {
                event: "inc".to_string(),
                label: Some("grd1".to_string())
            }
        );
        assert_eq!(published(findings)[0].range.start.line, line_of("@grd1"));

        // A label that resolves nowhere inside the event lands on its name.
        let findings = po_findings(&[po("m/inc/mystery/THM")], &closure);
        assert_eq!(
            published(findings)[0].range.start.line,
            line_of("EVENT inc")
        );

        // Unknown component: clicked machine header.
        let findings = po_findings(&[po("ghost/x/INV")], &closure);
        assert_eq!(findings[0].anchor, Anchor::MachineHeader);
        assert_eq!(published(findings)[0].range.start.line, 0);
    }

    #[test]
    fn new_run_replaces_and_empty_run_retracts() {
        let mut overlay = FindingsOverlay::default();
        let finding = Finding {
            uri: Url::parse("file:///m.eventb").unwrap(),
            component: "m".to_string(),
            anchor: Anchor::MachineHeader,
            code: "animate-deadlock",
            message: "Deadlock".to_string(),
        };
        assert!(overlay.apply("m".to_string(), AnimateMode::Check, vec![finding.clone()]));
        // The same findings again: nothing visible changed.
        assert!(!overlay.apply("m".to_string(), AnimateMode::Check, vec![finding.clone()]));
        // The po slot is independent of the check slot.
        assert!(overlay.apply("m".to_string(), AnimateMode::Po, vec![finding]));
        // A clean verdict retracts; retracting an absent slot is a no-op.
        assert!(overlay.apply("m".to_string(), AnimateMode::Check, Vec::new()));
        assert!(!overlay.apply("m".to_string(), AnimateMode::Check, Vec::new()));
        assert!(!overlay.is_empty(), "the po slot is still stored");
    }

    #[test]
    fn broken_parse_fallbacks_stay_inside_the_named_component() {
        // Two machines in one file, both declaring `@inv1` and an INVARIANTS
        // section; the trailing garbage breaks the parse so every anchor
        // resolves through the text scans. Findings for m1 must land in m1's
        // region, not on m0's identical label / section / header.
        let text = "MACHINE m0\nINVARIANTS\n    @inv1 x ∈ ℕ\nEND\nMACHINE m1\nINVARIANTS\n    @inv1 y ∈ ℕ\nEND\nMACHINE (\n";
        let doc = ParsedDocument::from_text(text.to_string());
        let uri = Url::parse("file:///m.eventb").unwrap();
        let finding = |anchor| Finding {
            uri: uri.clone(),
            component: "m1".to_string(),
            anchor,
            code: "animate-inv",
            message: "violated".to_string(),
        };
        let mut overlay = FindingsOverlay::default();
        overlay.apply(
            "m1".to_string(),
            AnimateMode::Check,
            vec![
                finding(Anchor::InvariantLabel("inv1".to_string())),
                finding(Anchor::InvariantsSection),
                finding(Anchor::MachineHeader),
            ],
        );
        let diags = animate_diagnostics(&uri, &doc, &overlay);
        assert_eq!(diags.len(), 3);
        assert_eq!(diags[0].range.start.line, 6, "m1's @inv1, not m0's");
        assert_eq!(diags[1].range.start.line, 5, "m1's INVARIANTS, not m0's");
        assert_eq!(diags[2].range.start.line, 4, "m1's header, not m0's");
    }

    #[test]
    fn anchors_survive_a_broken_parse_via_text_scans() {
        // Mid-edit text: unparsable, but the label and header lines exist.
        let text = "MACHINE m\nINVARIANTS\n    @inv1 x ∈ (\nEND\n";
        let doc = ParsedDocument::from_text(text.to_string());
        let mut overlay = FindingsOverlay::default();
        overlay.apply(
            "m".to_string(),
            AnimateMode::Check,
            vec![Finding {
                uri: Url::parse("file:///m.eventb").unwrap(),
                component: "m".to_string(),
                anchor: Anchor::InvariantLabel("inv1".to_string()),
                code: "animate-inv",
                message: "violated".to_string(),
            }],
        );
        let diags = animate_diagnostics(&Url::parse("file:///m.eventb").unwrap(), &doc, &overlay);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].range.start.line, 2, "the @inv1 text line");
    }
}

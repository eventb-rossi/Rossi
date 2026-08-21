//! Declaration type inlay hints: inferred types rendered at declaration
//! sites, computed over the document's dependency closure from current
//! buffer snapshots.

use std::sync::Arc;

use eventb_lsp::config::RossiConfig;
use eventb_lsp::cross_references::CrossReferenceManager;
use eventb_lsp::document::DocumentManager;
use eventb_lsp::inlay_hints::InlayHintsProvider;
use eventb_lsp::lsp_types::{
    InlayHint, InlayHintKind, InlayHintLabel, InlayHintTooltip, Position, Range,
    TextDocumentContentChangeEvent, Url,
};
use eventb_lsp::position::offset_to_position;

struct Fixture {
    documents: Arc<DocumentManager>,
    manager: Arc<CrossReferenceManager>,
    provider: InlayHintsProvider,
}

impl Fixture {
    fn new() -> Self {
        let documents = Arc::new(DocumentManager::new());
        let manager = Arc::new(CrossReferenceManager::new());
        let provider = InlayHintsProvider::new(Arc::clone(&documents), Arc::clone(&manager));
        Self {
            documents,
            manager,
            provider,
        }
    }

    fn open(&self, uri: &str, text: &str) -> Url {
        let url = Url::parse(uri).unwrap();
        self.manager.update_component(uri.to_string(), text);
        self.documents.open(url.clone(), 1, text.to_string());
        url
    }

    fn hints(&self, uri: &Url, config: &Arc<RossiConfig>) -> Vec<InlayHint> {
        self.provider
            .inlay_hints(uri, full_range(), config)
            .expect("document is open")
    }
}

fn full_range() -> Range {
    Range::new(Position::new(0, 0), Position::new(u32::MAX, u32::MAX))
}

fn default_config() -> Arc<RossiConfig> {
    Arc::new(RossiConfig::default())
}

/// The `(position, label)` pairs of `hints`, with positions resolved back
/// against `text` for readable assertions.
fn labels_at(hints: &[InlayHint], text: &str, name: &str) -> Vec<String> {
    let mut labels = Vec::new();
    let mut offset = 0;
    while let Some(found) = text[offset..].find(name) {
        let end = offset + found + name.len();
        let position = offset_to_position(text, end);
        for hint in hints {
            if hint.position == position {
                let InlayHintLabel::String(label) = &hint.label else {
                    panic!("string label expected");
                };
                labels.push(label.clone());
            }
        }
        offset = end;
    }
    labels
}

fn label_text(hint: &InlayHint) -> &str {
    match &hint.label {
        InlayHintLabel::String(label) => label,
        InlayHintLabel::LabelParts(_) => panic!("string label expected"),
    }
}

fn tooltip_text(hint: &InlayHint) -> Option<&str> {
    match &hint.tooltip {
        Some(InlayHintTooltip::String(text)) => Some(text),
        Some(InlayHintTooltip::MarkupContent(_)) => panic!("string tooltip expected"),
        None => None,
    }
}

#[test]
fn machine_variables_are_hinted_at_their_declaration() {
    let fixture = Fixture::new();
    let text = "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x ∈ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 x := 0\n    END\nEND\n";
    let uri = fixture.open("file:///m.eventb", text);

    let hints = fixture.hints(&uri, &default_config());

    assert_eq!(hints.len(), 1, "one variable, one hint: {hints:?}");
    let declaration_end = offset_to_position(text, text.find("    x\n").unwrap() + 5);
    assert_eq!(hints[0].position, declaration_end);
    assert_eq!(label_text(&hints[0]), ": ℤ");
    assert_eq!(hints[0].kind, Some(InlayHintKind::TYPE));
    assert_eq!(tooltip_text(&hints[0]), None);
}

#[test]
fn event_parameters_are_hinted_from_their_guards() {
    let fixture = Fixture::new();
    let text = "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x ∈ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 x := 0\n    END\n    EVENT step\n    ANY\n        p\n    WHERE\n        @grd1 p ∈ ℤ ↔ ℤ\n    THEN\n        @act1 x := x + 1\n    END\nEND\n";
    let uri = fixture.open("file:///m.eventb", text);

    let hints = fixture.hints(&uri, &default_config());

    assert_eq!(
        labels_at(&hints, text, "p"),
        vec![": ℙ(ℤ×ℤ)"],
        "the relation-typed parameter is hinted at its ANY declaration"
    );
}

#[test]
fn constants_are_hinted_and_carrier_sets_are_not() {
    let fixture = Fixture::new();
    let text = "CONTEXT c\nSETS\n    S\nCONSTANTS\n    k\nAXIOMS\n    @axm1 k ∈ S\nEND\n";
    let uri = fixture.open("file:///c.eventb", text);

    let hints = fixture.hints(&uri, &default_config());

    assert_eq!(hints.len(), 1, "the carrier set gets no hint: {hints:?}");
    assert_eq!(labels_at(&hints, text, "k"), vec![": S"]);
}

#[test]
fn seen_context_types_resolve_across_files() {
    let fixture = Fixture::new();
    fixture.open(
        "file:///c.eventb",
        "CONTEXT c\nSETS\n    S\nCONSTANTS\n    k\nAXIOMS\n    @axm1 k ∈ S\nEND\n",
    );
    let text = "MACHINE m\nSEES\n    c\nVARIABLES\n    v\nINVARIANTS\n    @inv1 v ⊆ S\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 v := ∅\n    END\nEND\n";
    let uri = fixture.open("file:///m.eventb", text);

    let hints = fixture.hints(&uri, &default_config());

    assert_eq!(labels_at(&hints, text, "v"), vec![": ℙ(S)"]);
}

#[test]
fn refinement_hints_only_declaration_sites_in_this_file() {
    let fixture = Fixture::new();
    fixture.open(
        "file:///abstract.eventb",
        "MACHINE abstract\nVARIABLES\n    kept\n    dropped\nINVARIANTS\n    @inv1 kept ∈ ℤ\n    @inv2 dropped ∈ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 kept := 0\n        @act2 dropped := 0\n    END\nEND\n",
    );
    // `kept` is redeclared (its typing invariant lives one machine up);
    // `dropped` is not redeclared and must not be hinted here.
    let text = "MACHINE concrete\nREFINES\n    abstract\nVARIABLES\n    kept\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 kept := 0\n    END\nEND\n";
    let uri = fixture.open("file:///concrete.eventb", text);

    let hints = fixture.hints(&uri, &default_config());

    assert_eq!(hints.len(), 1, "{hints:?}");
    let declaration_end = offset_to_position(text, text.find("    kept\n").unwrap() + 8);
    assert_eq!(hints[0].position, declaration_end);
    assert_eq!(label_text(&hints[0]), ": ℤ");
}

#[test]
fn untypeable_declarations_are_skipped_but_siblings_are_hinted() {
    let fixture = Fixture::new();
    let text = "MACHINE m\nVARIABLES\n    typed\n    mystery\nINVARIANTS\n    @inv1 typed ∈ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 typed := 0\n    END\nEND\n";
    let uri = fixture.open("file:///m.eventb", text);

    let hints = fixture.hints(&uri, &default_config());

    assert_eq!(labels_at(&hints, text, "typed"), vec![": ℤ"]);
    assert_eq!(labels_at(&hints, text, "mystery"), Vec::<String>::new());
}

#[test]
fn a_broken_sibling_component_does_not_suppress_healthy_hints() {
    let fixture = Fixture::new();
    let text = "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x ∈ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 x := 0\n    END\nEND\n\nMACHINE broken\nVARIABLES\n    +\nEND\n";
    let uri = fixture.open("file:///m.eventb", text);

    let hints = fixture.hints(&uri, &default_config());

    assert_eq!(labels_at(&hints, text, "x"), vec![": ℤ"]);
}

#[test]
fn hints_are_clipped_to_the_requested_range() {
    let fixture = Fixture::new();
    let text = "MACHINE m\nVARIABLES\n    x\n    y\nINVARIANTS\n    @inv1 x ∈ ℤ\n    @inv2 y ∈ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 x := 0\n        @act2 y := 0\n    END\nEND\n";
    let uri = fixture.open("file:///m.eventb", text);
    let config = default_config();

    let all = fixture
        .provider
        .inlay_hints(&uri, full_range(), &config)
        .unwrap();
    assert_eq!(all.len(), 2);

    // Only the line declaring `x`.
    let clipped = fixture
        .provider
        .inlay_hints(
            &uri,
            Range::new(Position::new(2, 0), Position::new(3, 0)),
            &config,
        )
        .unwrap();
    assert_eq!(clipped.len(), 1);
    assert_eq!(clipped[0].position.line, 2);
}

#[test]
fn long_types_truncate_with_the_full_type_as_tooltip() {
    let fixture = Fixture::new();
    let text = "MACHINE m\nVARIABLES\n    r\nINVARIANTS\n    @inv1 r ∈ ℤ ↔ (ℤ ↔ (ℤ ↔ ℤ))\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 r := ∅\n    END\nEND\n";
    let uri = fixture.open("file:///m.eventb", text);
    let full_type = "ℙ(ℤ×ℙ(ℤ×ℙ(ℤ×ℤ)))";

    let mut truncating = RossiConfig::default();
    truncating.inlay_hints.max_length = 8;
    let hints = fixture.hints(&uri, &Arc::new(truncating));
    assert_eq!(hints.len(), 1);
    let expected: String = full_type.chars().take(7).collect();
    assert_eq!(label_text(&hints[0]), format!(": {expected}…"));
    assert_eq!(tooltip_text(&hints[0]), Some(full_type));

    let mut untruncated = RossiConfig::default();
    untruncated.inlay_hints.max_length = 0;
    let hints = fixture.hints(&uri, &Arc::new(untruncated));
    assert_eq!(label_text(&hints[0]), format!(": {full_type}"));
    assert_eq!(tooltip_text(&hints[0]), None);
}

#[test]
fn ascii_configuration_renders_ascii_type_spellings() {
    let fixture = Fixture::new();
    let text = "MACHINE m\nVARIABLES\n    s\nINVARIANTS\n    @inv1 s ⊆ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 s := ∅\n    END\nEND\n";
    let uri = fixture.open("file:///m.eventb", text);

    let mut ascii = RossiConfig::default();
    ascii.format.use_unicode = false;
    let hints = fixture.hints(&uri, &Arc::new(ascii));

    assert_eq!(hints.len(), 1);
    assert_eq!(label_text(&hints[0]), ": POW(INT)");
}

#[test]
fn an_edit_invalidates_the_cached_hints() {
    let fixture = Fixture::new();
    let uri = fixture.open(
        "file:///m.eventb",
        "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x ∈ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 x := 0\n    END\nEND\n",
    );
    let config = default_config();

    let before = fixture.hints(&uri, &config);
    assert_eq!(label_text(&before[0]), ": ℤ");

    let retyped = "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x ⊆ ℤ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        @act1 x := ∅\n    END\nEND\n";
    fixture.documents.change(
        &uri,
        2,
        vec![TextDocumentContentChangeEvent {
            range: None,
            range_length: None,
            text: retyped.to_string(),
        }],
    );

    let after = fixture.hints(&uri, &config);
    assert_eq!(label_text(&after[0]), ": ℙ(ℤ)");
}

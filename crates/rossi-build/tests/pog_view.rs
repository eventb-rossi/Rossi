//! The normalized `.bpo` view: chain flattening, handle
//! normalization, and ascription-insensitive predicate comparison.

use rossi_build::po_view::{PoHint, PoView};
use rossi_build::sc_view::strip_type_ascriptions_pred;
use rossi_build::{Project, ProjectComponent, build_with_model};

fn machine_view(components: Vec<(&str, &str)>, file: &str) -> PoView {
    let components = components
        .into_iter()
        .map(|(name, body)| ProjectComponent::from_xml(name, body).unwrap())
        .collect();
    let project = Project::new("prj", components);
    let (build, _) = build_with_model(&project);
    assert!(build.is_ok(), "build diagnostics: {:?}", build.diagnostics);
    PoView::from_xml(&build.file(file).expect(file).contents).unwrap()
}

const M0: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_a" org.eventb.core.identifier="a"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="a ≥ 0"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_ia" org.eventb.core.assignment="a ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_evt" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd1" org.eventb.core.predicate="a &lt; 10"/>
<org.eventb.core.action name="_ea" org.eventb.core.assignment="a ≔ a + 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

#[test]
fn flattens_the_hypothesis_chain_root_first() {
    let view = machine_view(vec![("M0.bum", M0)], "M0.bpo");

    // evt/inv1/INV: chain CTXHYP → ABSHYP → ALLHYP → EVTIDENT →
    // EVTALLHYP. Flattened hypotheses: the invariant (ALLHYP), then the
    // guard (EVTALLHYP).
    let hyps = view.flattened_hypotheses("evt/inv1/INV");
    let rendered: Vec<String> = hyps
        .iter()
        .map(|h| rossi_build::normalize::canonical_predicate(&h.predicate))
        .collect();
    assert_eq!(rendered, vec!["a≥0", "a<10"], "in {view:#?}");

    // The identifiers include the variable and its primed after-value.
    let idents = view.flattened_identifiers("evt/inv1/INV");
    assert_eq!(idents.get("a"), Some(&"ℤ"));
    assert_eq!(idents.get("a'"), Some(&"ℤ"));

    // INITIALISATION roots at CTXHYP: no invariant hypothesis.
    let init_hyps = view.flattened_hypotheses("INITIALISATION/inv1/INV");
    assert!(init_hyps.is_empty(), "{init_hyps:?}");
}

#[test]
fn sequent_metadata_and_normalized_handles() {
    let view = machine_view(vec![("M0.bum", M0)], "M0.bpo");
    let sequent = &view.sequents["evt/inv1/INV"];
    assert_eq!(sequent.description, "Invariant  preservation");
    assert!(sequent.accurate);
    // Sources drop the leading /prj/ project segment.
    assert_eq!(
        sequent.sources[0],
        (
            "DEFAULT".to_string(),
            Some("M0.bum|org.eventb.core.machineFile#M0|org.eventb.core.event#_evt".to_string())
        )
    );
    // The predicate selection hint resolved to a normalized handle.
    assert!(sequent.hints.iter().any(|h| matches!(
        h,
        PoHint::Predicate(target)
            if target == "M0.bpo|org.eventb.core.poFile#M0|org.eventb.core.poPredicateSet#ALLHYP|org.eventb.core.poPredicate#PRD0"
    )));
}

#[test]
fn predicate_comparison_ignores_type_ascriptions() {
    let ascribed = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.poFile org.eventb.core.poStamp="3">
<org.eventb.core.poPredicateSet name="ABSHYP" org.eventb.core.poStamp="1">
<org.eventb.core.poPredicate name="l" org.eventb.core.predicate="S≠(∅ ⦂ ℙ(ℤ))" org.eventb.core.source="/other/C.buc|org.eventb.core.contextFile#C|org.eventb.core.axiom#'"/>
</org.eventb.core.poPredicateSet>
</org.eventb.core.poFile>"#;
    let bare = ascribed
        .replace("(∅ ⦂ ℙ(ℤ))", "∅")
        .replace("/other/", "/prj/")
        .replace(
            r#"org.eventb.core.poStamp="3""#,
            r#"org.eventb.core.poStamp="0""#,
        )
        .replace(
            r#"org.eventb.core.poStamp="1""#,
            r#"org.eventb.core.poStamp="0""#,
        );

    let a = PoView::from_xml(ascribed).unwrap();
    let b = PoView::from_xml(&bare).unwrap();
    // Ascriptions, stamps, and project names all normalize away.
    assert_eq!(
        a.sets["ABSHYP"].predicates, b.sets["ABSHYP"].predicates,
        "views must compare equal"
    );
    // And the stripped form equals a fresh parse.
    let expected = strip_type_ascriptions_pred(rossi::parse_predicate_str("S ≠ ∅").unwrap());
    assert_eq!(a.sets["ABSHYP"].predicates[0].predicate, expected);
}

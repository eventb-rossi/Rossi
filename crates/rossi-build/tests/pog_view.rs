//! The normalized `.bpo` view: chain flattening, handle
//! normalization, and ascription-insensitive predicate comparison.

mod common;

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

/// A small handwritten `.bpo`: a two-set chain, one sequent with a
/// local hypothesis and a goal, and stamps at every level.
const STAMPED: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.poFile org.eventb.core.poStamp="2">
<org.eventb.core.poPredicateSet name="CTXHYP" org.eventb.core.poStamp="0">
<org.eventb.core.poIdentifier name="a" org.eventb.core.type="ℤ"/>
<org.eventb.core.poIdentifier name="b" org.eventb.core.type="ℤ"/>
</org.eventb.core.poPredicateSet>
<org.eventb.core.poPredicateSet name="ALLHYP" org.eventb.core.parentSet="M.bpo|org.eventb.core.poFile#M|org.eventb.core.poPredicateSet#CTXHYP" org.eventb.core.poStamp="1">
<org.eventb.core.poPredicate name="PRD0" org.eventb.core.predicate="a≥0"/>
</org.eventb.core.poPredicateSet>
<org.eventb.core.poSequent name="evt/inv1/INV" org.eventb.core.accurate="true" org.eventb.core.poDesc="Invariant  preservation" org.eventb.core.poStamp="1">
<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="M.bpo|org.eventb.core.poFile#M|org.eventb.core.poPredicateSet#ALLHYP">
<org.eventb.core.poPredicate name="PRD0" org.eventb.core.predicate="a&lt;10"/>
</org.eventb.core.poPredicateSet>
<org.eventb.core.poPredicate name="SEQHYQ" org.eventb.core.predicate="a+1≥0"/>
</org.eventb.core.poSequent>
</org.eventb.core.poFile>"#;

#[test]
fn parses_stamps_verbatim_at_every_level() {
    let view = PoView::from_xml(STAMPED).unwrap();
    assert_eq!(view.stamp.as_deref(), Some("2"));
    assert_eq!(view.sets["CTXHYP"].stamp.as_deref(), Some("0"));
    assert_eq!(view.sets["ALLHYP"].stamp.as_deref(), Some("1"));
    assert_eq!(view.sequents["evt/inv1/INV"].stamp.as_deref(), Some("1"));

    // Absent stamps parse as None rather than a default.
    let unstamped = STAMPED
        .replace(r#" org.eventb.core.poStamp="2""#, "")
        .replace(r#" org.eventb.core.poStamp="1""#, "")
        .replace(r#" org.eventb.core.poStamp="0""#, "");
    let view = PoView::from_xml(&unstamped).unwrap();
    assert_eq!(view.stamp, None);
    assert_eq!(view.sets["ALLHYP"].stamp, None);
    assert_eq!(view.sequents["evt/inv1/INV"].stamp, None);
}

/// The corpus gates' per-field diff over the same pair — `sequent_eq`
/// mirrors its field set, and these tests keep the two from drifting.
fn diff_problems(reference: &PoView, ours: &PoView) -> Vec<String> {
    let mut problems = Vec::new();
    common::diff_po_views("pair", reference, ours, usize::MAX, &mut problems);
    problems
}

#[test]
fn sequent_eq_ignores_cosmetic_respelling() {
    let base = PoView::from_xml(STAMPED).unwrap();

    // Stamps, whitespace, ascriptions, identifier order, and where the
    // chain is cut all normalize away.
    let respelled = STAMPED
        .replace(r#"poStamp="2""#, r#"poStamp="7""#)
        .replace("a≥0", "a ≥ 0")
        .replace("a+1≥0", "(a ⦂ ℤ)+1≥0")
        .replace(
            "<org.eventb.core.poIdentifier name=\"a\" org.eventb.core.type=\"ℤ\"/>\n<org.eventb.core.poIdentifier name=\"b\" org.eventb.core.type=\"ℤ\"/>",
            "<org.eventb.core.poIdentifier name=\"b\" org.eventb.core.type=\"ℤ\"/>\n<org.eventb.core.poIdentifier name=\"a\" org.eventb.core.type=\"ℤ\"/>",
        );
    let other = PoView::from_xml(&respelled).unwrap();
    assert!(base.sequent_eq(&other, "evt/inv1/INV"));
    assert_eq!(diff_problems(&base, &other), Vec::<String>::new());

    // Moving the hypothesis one set up the chain keeps the flattened
    // content identical: the sequent is unchanged, the moved-into set
    // is not.
    let recut = STAMPED
        .replace(
            "<org.eventb.core.poIdentifier name=\"b\" org.eventb.core.type=\"ℤ\"/>\n</org.eventb.core.poPredicateSet>",
            "<org.eventb.core.poIdentifier name=\"b\" org.eventb.core.type=\"ℤ\"/>\n<org.eventb.core.poPredicate name=\"PRD0\" org.eventb.core.predicate=\"a≥0\"/>\n</org.eventb.core.poPredicateSet>",
        )
        .replace(
            "<org.eventb.core.poPredicate name=\"PRD0\" org.eventb.core.predicate=\"a≥0\"/>\n</org.eventb.core.poPredicateSet>\n<org.eventb.core.poSequent",
            "</org.eventb.core.poPredicateSet>\n<org.eventb.core.poSequent",
        );
    let other = PoView::from_xml(&recut).unwrap();
    assert!(other.sets["ALLHYP"].predicates.is_empty(), "{other:#?}");
    assert!(base.sequent_eq(&other, "evt/inv1/INV"));
    assert_eq!(diff_problems(&base, &other), Vec::<String>::new());
    assert!(!base.set_chain_eq(&other, "CTXHYP"));
}

#[test]
fn sequent_eq_detects_content_changes() {
    let base = PoView::from_xml(STAMPED).unwrap();
    let cases = [
        ("a+1≥0", "a+1≥1"),     // goal
        ("a&lt;10", "a&lt;11"), // local hypothesis
        ("a≥0", "b≥0"),         // chained hypothesis
        (
            r#"name="a" org.eventb.core.type="ℤ""#,
            r#"name="a" org.eventb.core.type="ℙ(ℤ)""#,
        ),
        ("Invariant  preservation", "Feasibility"), // nature
        (r#"accurate="true""#, r#"accurate="false""#),
    ];
    for (from, to) in cases {
        let other = PoView::from_xml(&STAMPED.replace(from, to)).unwrap();
        assert!(
            !base.sequent_eq(&other, "evt/inv1/INV"),
            "{from} -> {to} must count as a change"
        );
        assert!(
            !diff_problems(&base, &other).is_empty(),
            "{from} -> {to} must also surface in the per-field diff"
        );
    }
    // A sequent absent from either side is never "unchanged".
    assert!(!base.sequent_eq(&base, "no/such/PO"));
}

#[test]
fn set_chain_eq_propagates_ancestor_changes() {
    let base = PoView::from_xml(STAMPED).unwrap();
    // Changing CTXHYP content also invalidates the dependent ALLHYP...
    let other = PoView::from_xml(&STAMPED.replace(
        r#"name="b" org.eventb.core.type="ℤ""#,
        r#"name="c" org.eventb.core.type="ℤ""#,
    ))
    .unwrap();
    assert!(!base.set_chain_eq(&other, "CTXHYP"));
    assert!(!base.set_chain_eq(&other, "ALLHYP"));
    // ...while a pure stamp difference invalidates neither.
    let restamped = PoView::from_xml(&STAMPED.replace(r#"poStamp="1""#, r#"poStamp="9""#)).unwrap();
    assert!(base.set_chain_eq(&restamped, "CTXHYP"));
    assert!(base.set_chain_eq(&restamped, "ALLHYP"));
}

//! Refinement proof obligations: witness feasibility and the
//! witness-mediated invariant goals of refined events.

use rossi_build::{Project, ProjectComponent, build_with_model, pog};

fn generate(name: &str, components: Vec<ProjectComponent>) -> Vec<rossi_build::ScFile> {
    let project = Project::new(name, components);
    let (build, model) = build_with_model(&project);
    assert!(build.is_ok(), "build diagnostics: {:?}", build.diagnostics);
    pog::generate(&project, &model)
}

fn xml(filename: &str, body: &str) -> ProjectComponent {
    ProjectComponent::from_xml(filename, body).unwrap()
}

fn find<'a>(files: &'a [rossi_build::ScFile], name: &str) -> &'a rossi_build::ScFile {
    files.iter().find(|f| f.filename == name).unwrap()
}

const M0: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_a" org.eventb.core.identifier="a"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="a ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_ia" org.eventb.core.assignment="a ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_evt" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd1" org.eventb.core.predicate="a &lt; 10"/>
<org.eventb.core.action name="_ea" org.eventb.core.assignment="a :∣ a' &gt; a" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

const M1: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r" org.eventb.core.target="M0"/>
<org.eventb.core.variable name="_b" org.eventb.core.identifier="b"/>
<org.eventb.core.invariant name="_j1" org.eventb.core.label="inv2" org.eventb.core.predicate="b = a + 1"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_ja" org.eventb.core.assignment="b ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_evt" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.refinesEvent name="_re" org.eventb.core.target="evt"/>
<org.eventb.core.guard name="_h1" org.eventb.core.label="grd1" org.eventb.core.predicate="b &lt; 11"/>
<org.eventb.core.witness name="_w1" org.eventb.core.label="a'" org.eventb.core.predicate="a' &lt; b'"/>
<org.eventb.core.action name="_ja" org.eventb.core.assignment="b :∣ b' &gt; b" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

#[test]
fn nondeterministic_witness_needs_feasibility() {
    let files = generate("prj", vec![xml("M0.bum", M0), xml("M1.bum", M1)]);
    let contents = &find(&files, "M1.bpo").contents;

    // The witness for the dropped after-value a' is nondeterministic:
    // its feasibility binds a' existentially. Well-definedness is
    // trivial and produces nothing.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poSequent name="evt/a'/WFIS" org.eventb.core.accurate="true" org.eventb.core.poDesc="Feasibility of witness" org.eventb.core.poStamp="0">"#
        ),
        "in:\n{contents}"
    );
    assert!(
        contents.contains(r#"org.eventb.core.predicate="∃a'⦂ℤ·a'&lt;b'""#),
        "in:\n{contents}"
    );
    assert!(!contents.contains("/WWD"));
}

#[test]
fn refined_event_invariant_goes_through_the_witness() {
    let files = generate("prj", vec![xml("M0.bum", M0), xml("M1.bum", M1)]);
    let contents = &find(&files, "M1.bpo").contents;

    // The glue invariant b = a + 1 over the after-state: b primes to
    // b', the dropped a renames to a' through the nondeterministic
    // witness.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poSequent name="evt/inv2/INV" org.eventb.core.accurate="true" org.eventb.core.poDesc="Invariant  preservation" org.eventb.core.poStamp="0">"#
        ),
        "in:\n{contents}"
    );
    assert!(contents.contains(r#"org.eventb.core.predicate="b'=a'+1""#));
    // Local hypotheses: the witness predicate (its identifier occurs in
    // the goal) and the nondeterministic before-after predicate.
    assert!(contents.contains(r#"org.eventb.core.predicate="a'&lt;b'" org.eventb.core.source="/prj/M1.bum|org.eventb.core.machineFile#M1|org.eventb.core.event#_evt|org.eventb.core.witness#_w1""#));
    assert!(contents.contains(r#"org.eventb.core.predicate="b'&gt;b""#));
    // Sources carry the abstract/concrete event pair.
    assert!(contents.contains(
        r#"org.eventb.core.poRole="ABSTRACT" org.eventb.core.source="/prj/M0.bum|org.eventb.core.machineFile#M0|org.eventb.core.event#_evt""#
    ));
    assert!(contents.contains(
        r#"org.eventb.core.poRole="CONCRETE" org.eventb.core.source="/prj/M1.bum|org.eventb.core.machineFile#M1|org.eventb.core.event#_evt""#
    ));
}

#[test]
fn deterministic_abstract_initialisation_acts_as_witness() {
    let files = generate("prj", vec![xml("M0.bum", M0), xml("M1.bum", M1)]);
    let contents = &find(&files, "M1.bpo").contents;

    // INITIALISATION: the abstract a ≔ 0 substitutes for the dropped a,
    // the concrete b ≔ 1 for b' — invariant establishment 1 = 0 + 1.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poSequent name="INITIALISATION/inv2/INV" org.eventb.core.accurate="true" org.eventb.core.poDesc="Invariant  establishment" org.eventb.core.poStamp="0">"#
        ),
        "in:\n{contents}"
    );
    assert!(contents.contains(r#"org.eventb.core.predicate="1=0+1""#));
}

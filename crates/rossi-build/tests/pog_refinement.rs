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

#[test]
fn abstract_guards_must_be_strengthened() {
    let files = generate("prj", vec![xml("M0.bum", M0), xml("M1.bum", M1)]);
    let contents = &find(&files, "M1.bpo").contents;

    // The abstract guard a < 10 has no concrete counterpart: it must
    // follow from the concrete guards.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poSequent name="evt/grd1/GRD" org.eventb.core.accurate="true" org.eventb.core.poDesc="Guard strengthening (split)" org.eventb.core.poStamp="0">"#
        ),
        "in:\n{contents}"
    );
    assert!(contents.contains(
        r#"org.eventb.core.predicate="a&lt;10" org.eventb.core.source="/prj/M0.bum|org.eventb.core.machineFile#M0|org.eventb.core.event#_evt|org.eventb.core.guard#_g1""#
    ));
}

#[test]
fn abstract_actions_must_be_simulated() {
    let files = generate("prj", vec![xml("M0.bum", M0), xml("M1.bum", M1)]);
    let contents = &find(&files, "M1.bpo").contents;

    // The abstract a :∣ a' > a survives on the dropped a: its
    // before-after predicate must follow, through the witness.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poSequent name="evt/act1/SIM" org.eventb.core.accurate="true" org.eventb.core.poDesc="Action simulation" org.eventb.core.poStamp="0">"#
        ),
        "in:\n{contents}"
    );
    assert!(contents.contains(
        r#"org.eventb.core.predicate="a'&gt;a" org.eventb.core.source="/prj/M0.bum|org.eventb.core.machineFile#M0|org.eventb.core.event#_evt|org.eventb.core.action#_ea""#
    ));
}

const M0_KEEP: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_c" org.eventb.core.identifier="c"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="c ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_ia" org.eventb.core.assignment="c ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_evt" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd1" org.eventb.core.predicate="c &lt; 10"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

const M1_KEEP: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r" org.eventb.core.target="M0"/>
<org.eventb.core.variable name="_c" org.eventb.core.identifier="c"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION"/>
<org.eventb.core.event name="_evt" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.refinesEvent name="_re" org.eventb.core.target="evt"/>
<org.eventb.core.guard name="_h1" org.eventb.core.label="grd1" org.eventb.core.predicate="c &lt; 10"/>
<org.eventb.core.action name="_ka" org.eventb.core.assignment="c ≔ c + 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

#[test]
fn changing_an_abstractly_untouched_variable_needs_equality() {
    let files = generate("prj", vec![xml("M0.bum", M0_KEEP), xml("M1.bum", M1_KEEP)]);
    let contents = &find(&files, "M1.bpo").contents;

    // The abstract event leaves c alone; the concrete one assigns it.
    // The after-value must equal the before-value.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poSequent name="evt/c/EQL" org.eventb.core.accurate="true" org.eventb.core.poDesc="Equality of common variables" org.eventb.core.poStamp="0">"#
        ),
        "in:\n{contents}"
    );
    assert!(contents.contains(r#"org.eventb.core.predicate="c+1=c""#));
}

const MA_DROP: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_v" org.eventb.core.identifier="v"/>
<org.eventb.core.variable name="_w" org.eventb.core.identifier="w"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="v ∈ ℤ"/>
<org.eventb.core.invariant name="_i2" org.eventb.core.label="inv2" org.eventb.core.predicate="w ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_iv" org.eventb.core.assignment="v ≔ 0" org.eventb.core.label="act1"/>
<org.eventb.core.action name="_iw" org.eventb.core.assignment="w ≔ 0" org.eventb.core.label="act2"/>
</org.eventb.core.event>
<org.eventb.core.event name="_evt" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd1" org.eventb.core.predicate="w &lt; 10"/>
<org.eventb.core.action name="_ea" org.eventb.core.assignment="w ≔ w + 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

const MB_DROP: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r" org.eventb.core.target="MA"/>
<org.eventb.core.variable name="_w" org.eventb.core.identifier="w"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.witness name="_wv" org.eventb.core.label="v'" org.eventb.core.predicate="v' = 0"/>
<org.eventb.core.action name="_iw" org.eventb.core.assignment="w ≔ 0" org.eventb.core.label="act2"/>
</org.eventb.core.event>
<org.eventb.core.event name="_evt" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.refinesEvent name="_re" org.eventb.core.target="evt"/>
<org.eventb.core.guard name="_h1" org.eventb.core.label="grd1" org.eventb.core.predicate="w &lt; 10"/>
<org.eventb.core.guard name="_ht" org.eventb.core.label="thm1" org.eventb.core.predicate="v &gt; 0" org.eventb.core.theorem="true"/>
<org.eventb.core.action name="_ea" org.eventb.core.assignment="w ≔ w + 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

#[test]
fn theorem_guard_over_disappearing_variable_gets_a_theorem_obligation() {
    let files = generate("prj", vec![xml("MA.bum", MA_DROP), xml("MB.bum", MB_DROP)]);
    let contents = &find(&files, "MB.bpo").contents;

    // The theorem guard reads the dropped `v`; it survives the check and
    // must be proved like any other theorem guard, in a sequent that
    // stays accurate.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poSequent name="evt/thm1/THM" org.eventb.core.accurate="true" org.eventb.core.poDesc="Theorem" org.eventb.core.poStamp="0">"#
        ),
        "in:\n{contents}"
    );
    assert!(
        contents.contains(r#"org.eventb.core.predicate="v&gt;0""#),
        "in:\n{contents}"
    );
    // The dropped variable keeps its typed declaration in ABSHYP, so the
    // goal is well-typed for provers.
    assert!(
        contents.contains(r#"<org.eventb.core.poIdentifier name="v" org.eventb.core.type="ℤ"/>"#),
        "in:\n{contents}"
    );
    // Its well-definedness is trivial — no WD sequent.
    assert!(!contents.contains("evt/thm1/WD"), "in:\n{contents}");
}

const MA_MERGE: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_h" org.eventb.core.identifier="h"/>
<org.eventb.core.variable name="_w" org.eventb.core.identifier="w"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="h ∈ ℤ"/>
<org.eventb.core.invariant name="_i2" org.eventb.core.label="inv2" org.eventb.core.predicate="w ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_ih" org.eventb.core.assignment="h ≔ 0" org.eventb.core.label="act1"/>
<org.eventb.core.action name="_iw" org.eventb.core.assignment="w ≔ 0" org.eventb.core.label="act2"/>
</org.eventb.core.event>
<org.eventb.core.event name="_sh" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="setHeight">
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd" org.eventb.core.predicate="h = 0"/>
<org.eventb.core.action name="_a1" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
<org.eventb.core.action name="_a2" org.eventb.core.assignment="w ≔ 17" org.eventb.core.label="beta"/>
</org.eventb.core.event>
<org.eventb.core.event name="_sw" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="setWidth">
<org.eventb.core.guard name="_g2" org.eventb.core.label="grd" org.eventb.core.predicate="w = 0"/>
<org.eventb.core.guard name="_g3" org.eventb.core.label="thm" org.eventb.core.predicate="w ≥ 0 ∨ w &lt; 0" org.eventb.core.theorem="true"/>
<org.eventb.core.action name="_a3" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
<org.eventb.core.action name="_a4" org.eventb.core.assignment="w ≔ 17" org.eventb.core.label="beta"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

fn mb_merge(set_both_guard: &str) -> String {
    format!(
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r" org.eventb.core.target="MA"/>
<org.eventb.core.variable name="_h" org.eventb.core.identifier="h"/>
<org.eventb.core.variable name="_w" org.eventb.core.identifier="w"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION"/>
<org.eventb.core.event name="_sb" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="setBoth">
<org.eventb.core.refinesEvent name="_r1" org.eventb.core.target="setHeight"/>
<org.eventb.core.refinesEvent name="_r2" org.eventb.core.target="setWidth"/>
{set_both_guard}
<org.eventb.core.action name="_ba" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
<org.eventb.core.action name="_bb" org.eventb.core.assignment="w ≔ 17" org.eventb.core.label="beta"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#
    )
}

#[test]
fn merged_event_gets_the_disjunctive_obligation() {
    let mb = mb_merge(
        r#"<org.eventb.core.guard name="_g" org.eventb.core.label="grd" org.eventb.core.predicate="h = 0 ∨ w = 0"/>"#,
    );
    let files = generate("prj", vec![xml("MA.bum", MA_MERGE), xml("MB.bum", &mb)]);
    let contents = &find(&files, "MB.bpo").contents;

    // One disjunctive obligation: each abstract event's new non-theorem
    // guards as one disjunct. The abstract theorem guard is excluded.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poSequent name="setBoth/MRG" org.eventb.core.accurate="true" org.eventb.core.poDesc="Guard strengthening (merge)" org.eventb.core.poStamp="0">"#
        ),
        "in:\n{contents}"
    );
    assert!(
        contents.contains(r#"org.eventb.core.predicate="h=0∨w=0""#),
        "in:\n{contents}"
    );
    // Sources: one ABSTRACT per merged event, then the concrete event.
    assert!(contents.contains(
        r#"org.eventb.core.poRole="ABSTRACT" org.eventb.core.source="/prj/MA.bum|org.eventb.core.machineFile#MA|org.eventb.core.event#_sh""#
    ));
    assert!(contents.contains(
        r#"org.eventb.core.poRole="ABSTRACT" org.eventb.core.source="/prj/MA.bum|org.eventb.core.machineFile#MA|org.eventb.core.event#_sw""#
    ));
    assert!(contents.contains(
        r#"org.eventb.core.poRole="CONCRETE" org.eventb.core.source="/prj/MB.bum|org.eventb.core.machineFile#MB|org.eventb.core.event#_sb""#
    ));
    // The split path stays quiet for a merge.
    assert!(!contents.contains("/GRD"), "in:\n{contents}");
}

#[test]
fn merged_obligation_vanishes_when_a_branch_holds_concretely() {
    // The concrete event repeats setHeight's entire guard set, so that
    // branch is trivially true and the whole obligation is discharged.
    let mb = mb_merge(
        r#"<org.eventb.core.guard name="_g" org.eventb.core.label="grd" org.eventb.core.predicate="h = 0"/>"#,
    );
    let files = generate("prj", vec![xml("MA.bum", MA_MERGE), xml("MB.bum", &mb)]);
    let contents = &find(&files, "MB.bpo").contents;
    assert!(!contents.contains("setBoth/MRG"), "in:\n{contents}");
}

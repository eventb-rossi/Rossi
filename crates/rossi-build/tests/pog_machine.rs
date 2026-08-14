//! Machine-level proof obligations: invariant well-definedness and
//! theorems, the hypothesis stack (seen contexts, variables, inherited
//! invariants), and variant obligations.

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

#[test]
fn invariant_wd_and_theorem_obligations_with_seen_context() {
    let context = xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.constant name="_n" org.eventb.core.identifier="n"/>
<org.eventb.core.axiom name="_a1" org.eventb.core.label="axm1" org.eventb.core.predicate="n ∈ ℤ"/>
</org.eventb.core.contextFile>"#,
    );
    let machine = xml(
        "M.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.seesContext name="_s" org.eventb.core.target="C"/>
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.invariant name="_i2" org.eventb.core.label="inv2" org.eventb.core.predicate="10 ÷ x &gt; 0"/>
<org.eventb.core.invariant name="_t1" org.eventb.core.label="thm1" org.eventb.core.predicate="x + n &gt; x" org.eventb.core.theorem="true"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a" org.eventb.core.assignment="x ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    );
    let files = generate("prj", vec![context, machine]);
    let contents = &find(&files, "M.bpo").contents;

    for needle in [
        // CTXHYP: the seen context's constant and axiom.
        r#"<org.eventb.core.poPredicateSet name="CTXHYP" org.eventb.core.poStamp="0">"#,
        r#"<org.eventb.core.poIdentifier name="n" org.eventb.core.type="ℤ"/>"#,
        r#"org.eventb.core.predicate="n∈ℤ" org.eventb.core.source="/prj/C.buc|org.eventb.core.contextFile#C|org.eventb.core.axiom#_a1"/>"#,
        // ABSHYP chains on CTXHYP and carries the variable.
        r#"<org.eventb.core.poPredicateSet name="ABSHYP" org.eventb.core.parentSet="/prj/M.bpo|org.eventb.core.poFile#M|org.eventb.core.poPredicateSet#CTXHYP" org.eventb.core.poStamp="0">"#,
        r#"<org.eventb.core.poIdentifier name="x" org.eventb.core.type="ℤ"/>"#,
        // inv2's well-definedness, cutting after inv1.
        r#"<org.eventb.core.poSequent name="inv2/WD" org.eventb.core.accurate="true" org.eventb.core.poDesc="Well-definedness of Invariant" org.eventb.core.poStamp="0">"#,
        r#"org.eventb.core.predicate="x≠0""#,
        // thm1's provability.
        r#"<org.eventb.core.poSequent name="thm1/THM" org.eventb.core.accurate="true" org.eventb.core.poDesc="Theorem" org.eventb.core.poStamp="0">"#,
        // ALLHYP has all three invariants with global numbering.
        r#"<org.eventb.core.poPredicate name="PRD0" org.eventb.core.predicate="x∈ℤ""#,
        r#"<org.eventb.core.poPredicate name="PRD1" org.eventb.core.predicate="10 ÷ x&gt;0""#,
        r#"<org.eventb.core.poPredicate name="PRD2" org.eventb.core.predicate="x+n&gt;x""#,
    ] {
        assert!(
            contents.contains(needle),
            "missing {needle} in:\n{contents}"
        );
    }
    assert!(!contents.contains(r#"name="inv1/WD""#));
}

#[test]
fn inherited_invariants_become_plain_hypotheses() {
    let m0 = xml(
        "M0.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="x ≥ 0"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a" org.eventb.core.assignment="x ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    );
    let m1 = xml(
        "M1.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r" org.eventb.core.target="M0"/>
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_j1" org.eventb.core.label="inv2" org.eventb.core.predicate="x ≤ 100"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a" org.eventb.core.assignment="x ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    );
    let files = generate("prj", vec![m0, m1]);
    let contents = &find(&files, "M1.bpo").contents;

    // M0's invariant is a plain ABSHYP hypothesis with a generated name
    // (fresh after observing the variable "x"), tracing to M0's file.
    assert!(contents.contains(
        r#"<org.eventb.core.poPredicate name="y" org.eventb.core.predicate="x≥0" org.eventb.core.source="/prj/M0.bum|org.eventb.core.machineFile#M0|org.eventb.core.invariant#_i1"/>"#
    ), "in:\n{contents}");
    // Only M1's own invariant is in the incremental table.
    assert!(
        contents.contains(
            r#"<org.eventb.core.poPredicate name="PRD0" org.eventb.core.predicate="x≤100""#
        )
    );
    assert!(!contents.contains(r#"name="PRD1""#));
}

#[test]
fn variant_wd_and_finiteness() {
    // A set-typed variant with a division inside: both VWD and FIN.
    let machine = xml(
        "M.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.variant name="_v" org.eventb.core.expression="{10 ÷ x}"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a" org.eventb.core.assignment="x ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e" org.eventb.core.convergence="1" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.action name="_ea" org.eventb.core.assignment="x ≔ x + 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    );
    let files = generate("prj", vec![machine]);
    let contents = &find(&files, "M.bpo").contents;

    for needle in [
        // A single default-labelled variant omits the label segment.
        r#"<org.eventb.core.poSequent name="VWD" org.eventb.core.accurate="true" org.eventb.core.poDesc="Well-definedness of variant" org.eventb.core.poStamp="0">"#,
        r#"org.eventb.core.predicate="x≠0" org.eventb.core.source="/prj/M.bum|org.eventb.core.machineFile#M|org.eventb.core.variant#_v"/>"#,
        r#"<org.eventb.core.poSequent name="FIN" org.eventb.core.accurate="true" org.eventb.core.poDesc="Finiteness of variant" org.eventb.core.poStamp="0">"#,
        r#"org.eventb.core.predicate="finite({10 ÷ x})""#,
        // Variant obligations plug into the full hypothesis directly.
        r#"<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="/prj/M.bpo|org.eventb.core.poFile#M|org.eventb.core.poPredicateSet#ALLHYP"/>"#,
    ] {
        assert!(
            contents.contains(needle),
            "missing {needle} in:\n{contents}"
        );
    }
}

#[test]
fn integer_variant_needs_no_finiteness() {
    let machine = xml(
        "M.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.variant name="_v" org.eventb.core.expression="x" org.eventb.core.label="var1"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a" org.eventb.core.assignment="x ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e" org.eventb.core.convergence="1" org.eventb.core.extended="false" org.eventb.core.label="evt">
<org.eventb.core.action name="_ea" org.eventb.core.assignment="x ≔ x − 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    );
    let files = generate("prj", vec![machine]);
    let contents = &find(&files, "M.bpo").contents;

    // `x` is well-defined and integer-typed: no variant obligations at
    // all. (A labelled variant would prefix its label, pinned below by
    // the absence of any variant sequent.)
    assert!(!contents.contains("VWD"));
    assert!(!contents.contains("FIN"));
}

#[test]
fn convergent_events_decrease_the_variant() {
    let machine = xml(
        "M.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.variant name="_v" org.eventb.core.expression="x"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a" org.eventb.core.assignment="x ≔ 10" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_down" org.eventb.core.convergence="1" org.eventb.core.extended="false" org.eventb.core.label="down">
<org.eventb.core.action name="_da" org.eventb.core.assignment="x ≔ x − 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_wait" org.eventb.core.convergence="2" org.eventb.core.extended="false" org.eventb.core.label="wait">
<org.eventb.core.action name="_wa" org.eventb.core.assignment="x :∣ x' ≤ x" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    );
    let files = generate("prj", vec![machine]);
    let contents = &find(&files, "M.bpo").contents;

    for needle in [
        // The convergent event proves membership in ℕ and a strict
        // decrease of the after-value.
        r#"<org.eventb.core.poSequent name="down/NAT" org.eventb.core.accurate="true" org.eventb.core.poDesc="Natural number variant of event" org.eventb.core.poStamp="0">"#,
        r#"org.eventb.core.predicate="x∈ℕ""#,
        r#"<org.eventb.core.poSequent name="down/VAR" org.eventb.core.accurate="true" org.eventb.core.poDesc="Variant of event" org.eventb.core.poStamp="0">"#,
        r#"org.eventb.core.predicate="x − 1&lt;x""#,
        // The anticipated event must not increase it, with its
        // nondeterministic before-after predicate assumed.
        r#"<org.eventb.core.poSequent name="wait/VAR" org.eventb.core.accurate="true" org.eventb.core.poDesc="Variant of event" org.eventb.core.poStamp="0">"#,
        r#"org.eventb.core.predicate="x'≤x""#,
    ] {
        assert!(
            contents.contains(needle),
            "missing {needle} in:\n{contents}"
        );
    }
    // No NAT for the anticipated event, nothing for INITIALISATION.
    assert!(!contents.contains(r#"name="wait/NAT""#));
    assert!(!contents.contains(r#"name="INITIALISATION/VAR""#));
}

//! `check_with_model` produces the same typed model as `build_with_model`
//! while skipping proof-obligation generation.

use std::collections::BTreeSet;

use rossi_build::{Project, ProjectComponent, build_with_model, check_with_model};

fn project() -> Project {
    let context = ProjectComponent::from_xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.constant name="_n" org.eventb.core.identifier="n"/>
<org.eventb.core.axiom name="_type" org.eventb.core.label="type" org.eventb.core.predicate="n ∈ ℤ"/>
</org.eventb.core.contextFile>"#,
    )
    .unwrap();
    let machine = ProjectComponent::from_xml(
        "M.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.seesContext name="_see" org.eventb.core.target="C"/>
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_type" org.eventb.core.label="type" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_init_a" org.eventb.core.assignment="x ≔ n" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    )
    .unwrap();
    Project::new("check", vec![context, machine])
}

#[test]
fn skips_proof_obligation_files_but_keeps_the_typed_model() {
    let project = project();
    let (checked, check_model) = check_with_model(&project);
    let (built, build_model) = build_with_model(&project);

    assert!(checked.is_ok(), "diagnostics: {:?}", checked.diagnostics);
    let filenames = |files: &[rossi_build::ScFile]| -> Vec<String> {
        files.iter().map(|f| f.filename.clone()).collect()
    };
    assert_eq!(filenames(&checked.files), vec!["C.bcc", "M.bcm"]);
    assert_eq!(
        filenames(&built.files),
        vec!["C.bcc", "M.bcm", "C.bpo", "C.bps", "M.bpo", "M.bps"]
    );

    let keys = |model: &rossi_build::sc_model::ScModel| -> (BTreeSet<String>, BTreeSet<String>) {
        (
            model.contexts.keys().cloned().collect(),
            model.machines.keys().cloned().collect(),
        )
    };
    assert_eq!(keys(&check_model), keys(&build_model));
    assert_eq!(check_model.machines["M"].record.variables[0].name, "x");
}

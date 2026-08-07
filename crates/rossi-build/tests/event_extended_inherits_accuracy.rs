//! An EXTENDED event inherits its immediate abstract event's inaccuracy.
//!
//! Rodin marks an extended concrete event `accurate="false"` whenever the
//! abstract event it copies is itself inaccurate — the concrete event is no
//! longer a lossless reflection of the source. A plain (non-extended)
//! refinement does NOT inherit that flag: it re-states its own clauses.
//!
//! Isolation: the abstract event `INITIALISATION` is made inaccurate by the
//! untyped-variable lever (its action assigns an untyped variable, so the
//! action is dropped). The refining machine adds a typing invariant for the
//! same variable, so its own recomputation of the inherited action is clean.
//! Thus the concrete event is inaccurate *only* via inheritance.

use rossi_build::{Project, ProjectComponent, build, build_with_model, sc_view::ScView};

// Abstract machine: `x` has no typing invariant, so the INITIALISATION
// action `x ≔ 0` is dropped and INITIALISATION is inaccurate. The file
// itself stays accurate (event-level signal only).
const M0_BUM: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_v_x" org.eventb.core.identifier="x"/>
<org.eventb.core.event name="_init0" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a0" org.eventb.core.assignment="x ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

// Refines M0, redeclares `x` and types it via `x ∈ ℤ`, and extends
// INITIALISATION. M1's own recomputation of the inherited `x ≔ 0` succeeds
// (x is typed here), so any inaccuracy must come from inheriting M0.
const M1_EXTENDED_BUM: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_ref" org.eventb.core.target="M0"/>
<org.eventb.core.variable name="_v_x1" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i0" org.eventb.core.label="inv1" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init1" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION">
<org.eventb.core.refinesEvent name="_re_init" org.eventb.core.target="INITIALISATION"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

// Same isolation, but a NON-extended INITIALISATION that re-states its own
// (typed) action. It must NOT inherit M0's inaccuracy.
const M1_PLAIN_BUM: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_ref" org.eventb.core.target="M0"/>
<org.eventb.core.variable name="_v_x1" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i0" org.eventb.core.label="inv1" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init1" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a1" org.eventb.core.assignment="x ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

const M2_EXTENDED_BUM: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_ref" org.eventb.core.target="M1"/>
<org.eventb.core.variable name="_v_x2" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i0" org.eventb.core.label="inv1" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init2" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION">
<org.eventb.core.refinesEvent name="_re_init" org.eventb.core.target="INITIALISATION"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

fn extended_project() -> Project {
    Project::new(
        "ext",
        vec![
            ProjectComponent::from_xml("M0.bum", M0_BUM).unwrap(),
            ProjectComponent::from_xml("M1.bum", M1_EXTENDED_BUM).unwrap(),
        ],
    )
}

fn plain_project() -> Project {
    Project::new(
        "pln",
        vec![
            ProjectComponent::from_xml("M0.bum", M0_BUM).unwrap(),
            ProjectComponent::from_xml("M1.bum", M1_PLAIN_BUM).unwrap(),
        ],
    )
}

fn transitive_extended_project() -> Project {
    Project::new(
        "transitive",
        vec![
            ProjectComponent::from_xml("M0.bum", M0_BUM).unwrap(),
            ProjectComponent::from_xml("M1.bum", M1_EXTENDED_BUM).unwrap(),
            ProjectComponent::from_xml("M2.bum", M2_EXTENDED_BUM).unwrap(),
        ],
    )
}

#[test]
fn extended_event_inherits_abstract_inaccuracy() {
    let r = build(&extended_project());
    // Sanity: the abstract INITIALISATION is inaccurate, but M0 the file
    // stays accurate.
    let m0 = r.file("M0.bcm").expect("M0.bcm");
    assert!(
        m0.accurate,
        "M0 file should stay accurate; {:?}",
        r.diagnostics
    );
    let m0_view = ScView::from_xml(&m0.contents).unwrap();
    let m0_init = m0_view
        .events
        .get("INITIALISATION")
        .expect("INITIALISATION present");
    assert!(
        !m0_init.accurate,
        "M0 INITIALISATION should be inaccurate (untyped LHS); {:?}",
        r.diagnostics
    );
    let m1 = r.file("M1.bcm").expect("M1.bcm");
    let v = ScView::from_xml(&m1.contents).unwrap();
    let init = v
        .events
        .get("INITIALISATION")
        .expect("INITIALISATION present");
    assert!(
        !init.accurate,
        "extended INITIALISATION must inherit M0's inaccuracy; {:?}",
        r.diagnostics
    );
}

#[test]
fn extended_event_inherits_transitive_abstract_inaccuracy() {
    let r = build(&transitive_extended_project());
    let m2 = r.file("M2.bcm").expect("M2.bcm");
    let v = ScView::from_xml(&m2.contents).unwrap();
    let init = v
        .events
        .get("INITIALISATION")
        .expect("INITIALISATION present");
    assert!(
        !init.accurate,
        "extended INITIALISATION must inherit transitive inaccuracy; {:?}",
        r.diagnostics
    );
}

#[test]
fn plain_refinement_does_not_inherit_inaccuracy() {
    let r = build(&plain_project());
    let m1 = r.file("M1.bcm").expect("M1.bcm");
    let v = ScView::from_xml(&m1.contents).unwrap();
    let init = v
        .events
        .get("INITIALISATION")
        .expect("INITIALISATION present");
    assert!(
        init.accurate,
        "non-extended INITIALISATION re-states its own typed action and must \
         stay accurate; {:?}",
        r.diagnostics
    );
}

// --------------------------------------------------------------------
// Rendering inherited events whose concrete labels differ from their
// parents.
// --------------------------------------------------------------------

const RENAME_M0: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_v0" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i0" org.eventb.core.label="type0" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init0" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_init_act0" org.eventb.core.assignment="x ≔ 0" org.eventb.core.label="init0"/>
</org.eventb.core.event>
<org.eventb.core.event name="_event0" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="abstract_step">
<org.eventb.core.parameter name="_param0" org.eventb.core.identifier="p"/>
<org.eventb.core.guard name="_guard0" org.eventb.core.label="typed" org.eventb.core.predicate="p ∈ ℤ"/>
<org.eventb.core.action name="_action0" org.eventb.core.assignment="x ≔ p" org.eventb.core.label="write"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

const RENAME_M1: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_ref1" org.eventb.core.target="M0"/>
<org.eventb.core.variable name="_v1" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="type1" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init1" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION">
<org.eventb.core.refinesEvent name="_init_ref1" org.eventb.core.target="INITIALISATION"/>
</org.eventb.core.event>
<org.eventb.core.event name="_event1" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="middle_step">
<org.eventb.core.refinesEvent name="_event_ref1" org.eventb.core.target="abstract_step"/>
<org.eventb.core.guard name="_guard1" org.eventb.core.label="nonnegative" org.eventb.core.predicate="p ≥ 0"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

const RENAME_M2: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_ref2" org.eventb.core.target="M1"/>
<org.eventb.core.variable name="_v2" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i2" org.eventb.core.label="type2" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init2" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION">
<org.eventb.core.refinesEvent name="_init_ref2" org.eventb.core.target="INITIALISATION"/>
</org.eventb.core.event>
<org.eventb.core.event name="_event2" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="concrete_step">
<org.eventb.core.refinesEvent name="_event_ref2" org.eventb.core.target="middle_step"/>
<org.eventb.core.guard name="_guard2" org.eventb.core.label="bounded" org.eventb.core.predicate="p ≤ 10"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

fn rename_project() -> Project {
    Project::new(
        "rename",
        vec![
            ProjectComponent::from_xml("M0.bum", RENAME_M0).unwrap(),
            ProjectComponent::from_xml("M1.bum", RENAME_M1).unwrap(),
            ProjectComponent::from_xml("M2.bum", RENAME_M2).unwrap(),
        ],
    )
}

#[test]
fn event_inherited_rendering_uses_the_abstract_event_label() {
    let (result, model) = build_with_model(&rename_project());
    assert!(result.is_ok(), "diagnostics: {:?}", result.diagnostics);

    let middle = model.machines["M1"].events_by_label["middle_step"].as_ref();
    assert_eq!(
        middle.inherited.as_ref().map(|event| event.label.as_str()),
        Some("abstract_step")
    );
    let concrete = model.machines["M2"].events_by_label["concrete_step"].as_ref();
    assert_eq!(
        concrete
            .inherited
            .as_ref()
            .map(|event| event.label.as_str()),
        Some("middle_step")
    );

    let m2 = result.file("M2.bcm").expect("M2.bcm");
    let view = ScView::from_xml(&m2.contents).unwrap();
    let concrete = view.events.get("concrete_step").expect("concrete_step");
    assert!(concrete.accurate);
    assert!(concrete.extended);
    assert_eq!(concrete.parameters.len(), 1);
    assert_eq!(concrete.guards.len(), 3);
    assert_eq!(concrete.actions.len(), 1);
    assert_eq!(
        concrete.refines_events.values().next().map(String::as_str),
        Some("M1.bcm|org.eventb.core.scMachineFile#M1")
    );

    // The inherited INITIALISATION renders transitively too.
    let init = view.events.get("INITIALISATION").expect("INITIALISATION");
    assert!(init.accurate);
    assert!(init.extended);
    assert_eq!(init.actions.len(), 1);
}

//! Merged events: one concrete event refining several abstract events.
//! The merge is well-formed when the abstract events' actions are
//! identical (matched by label) and shared abstract parameter names
//! agree in type; violations are EB027 errors that keep the first
//! target's shape and mark the event inaccurate.

use rossi_build::{Project, RuleId, Severity, build, build_with_model};

mod common;
use common::xml;

/// Abstract machine in the shape of the classical merge example: two
/// events with identical actions, differing guards.
const MA: &str = r#"<?xml version="1.0"?>
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
<org.eventb.core.action name="_a3" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
<org.eventb.core.action name="_a4" org.eventb.core.assignment="w ≔ 17" org.eventb.core.label="beta"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;

/// A refinement of `MA` whose `setBoth` merges both abstract events.
fn mb(set_both_children: &str, extended: &str) -> String {
    format!(
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r" org.eventb.core.target="MA"/>
<org.eventb.core.variable name="_h" org.eventb.core.identifier="h"/>
<org.eventb.core.variable name="_w" org.eventb.core.identifier="w"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION"/>
<org.eventb.core.event name="_sb" org.eventb.core.convergence="0" org.eventb.core.extended="{extended}" org.eventb.core.label="setBoth">
{set_both_children}
</org.eventb.core.event>
</org.eventb.core.machineFile>"#
    )
}

const SET_BOTH_MERGE: &str = r#"<org.eventb.core.refinesEvent name="_r1" org.eventb.core.target="setHeight"/>
<org.eventb.core.refinesEvent name="_r2" org.eventb.core.target="setWidth"/>
<org.eventb.core.guard name="_g" org.eventb.core.label="grd" org.eventb.core.predicate="h = 0 ∨ w = 0"/>
<org.eventb.core.action name="_a1" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
<org.eventb.core.action name="_a2" org.eventb.core.assignment="w ≔ 17" org.eventb.core.label="beta"/>"#;

fn merge_errors(r: &rossi_build::BuildResult) -> Vec<String> {
    r.diagnostics
        .iter()
        .filter(|d| d.rule_id == Some(RuleId::EventMergeMismatch))
        .map(|d| d.message.clone())
        .collect()
}

#[test]
fn compatible_merge_keeps_both_targets() {
    let project = Project::new(
        "prj",
        vec![
            xml("MA.bum", MA),
            xml("MB.bum", &mb(SET_BOTH_MERGE, "false")),
        ],
    );
    let (r, model) = build_with_model(&project);
    assert!(r.is_ok(), "diagnostics: {:?}", r.diagnostics);
    assert!(merge_errors(&r).is_empty(), "{:?}", r.diagnostics);

    // Two ordered scRefinesEvent children reach the .bcm.
    let bcm = &r.file("MB.bcm").expect("MB.bcm").contents;
    let view = rossi_build::sc_view::ScView::from_xml(bcm).unwrap();
    let set_both = view.events.get("setBoth").expect("setBoth present");
    assert!(set_both.accurate, "merge stays accurate");
    assert_eq!(
        set_both.refines_events.len(),
        2,
        "two scRefinesEvent children: {:#?}",
        set_both.refines_events
    );
    let block_start = bcm.find(r#"label="setBoth""#).expect("setBoth element");
    let block = &bcm[block_start
        ..bcm[block_start..]
            .find("</org.eventb.core.scEvent>")
            .map_or(bcm.len(), |e| block_start + e)];
    assert_eq!(
        block.matches("<org.eventb.core.scRefinesEvent").count(),
        2,
        "in:\n{block}"
    );
    let first = block
        .find("org.eventb.core.refinesEvent#_r1")
        .expect("first clause identity");
    let second = block
        .find("org.eventb.core.refinesEvent#_r2")
        .expect("second clause identity");
    assert!(first < second, "declaration order preserved");

    // The checked model resolves both abstract events, in order.
    let machine = &model.machines["MB"];
    let event = machine.events_by_label["setBoth"].clone();
    let targets: Vec<&str> = model
        .abstract_events(machine, &event)
        .iter()
        .map(|e| e.label.as_str())
        .collect();
    assert_eq!(targets, vec!["setHeight", "setWidth"]);
}

#[test]
fn differing_abstract_actions_are_rejected() {
    // setWidth's beta assigns 18 instead of 17.
    let ma = MA.replace(
        r#"name="_a4" org.eventb.core.assignment="w ≔ 17""#,
        r#"name="_a4" org.eventb.core.assignment="w ≔ 18""#,
    );
    let project = Project::new(
        "prj",
        vec![
            xml("MA.bum", &ma),
            xml("MB.bum", &mb(SET_BOTH_MERGE, "false")),
        ],
    );
    let r = build(&project);
    let errors = merge_errors(&r);
    assert_eq!(errors.len(), 1, "{:?}", r.diagnostics);
    assert!(errors[0].contains("must be identical"), "{}", errors[0]);
    let view = rossi_build::sc_view::ScView::from_xml(&r.file("MB.bcm").unwrap().contents).unwrap();
    assert!(!view.events["setBoth"].accurate);
}

#[test]
fn differing_abstract_action_labels_are_rejected() {
    // setWidth carries the same assignments under swapped labels.
    let ma = MA.replace(
        r#"name="_a3" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa""#,
        r#"name="_a3" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="gamma""#,
    );
    let project = Project::new(
        "prj",
        vec![
            xml("MA.bum", &ma),
            xml("MB.bum", &mb(SET_BOTH_MERGE, "false")),
        ],
    );
    let r = build(&project);
    let errors = merge_errors(&r);
    assert_eq!(errors.len(), 1, "{:?}", r.diagnostics);
    assert!(errors[0].contains("labels"), "{}", errors[0]);
}

#[test]
fn conflicting_abstract_parameter_types_are_rejected() {
    let ma = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_h" org.eventb.core.identifier="h"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="h ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_ih" org.eventb.core.assignment="h ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e1" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evtP">
<org.eventb.core.parameter name="_p1" org.eventb.core.identifier="p"/>
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd" org.eventb.core.predicate="p ∈ ℕ"/>
<org.eventb.core.action name="_a1" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e2" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evtQ">
<org.eventb.core.parameter name="_p2" org.eventb.core.identifier="p"/>
<org.eventb.core.guard name="_g2" org.eventb.core.label="grd" org.eventb.core.predicate="p = TRUE"/>
<org.eventb.core.action name="_a2" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;
    let mb = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r" org.eventb.core.target="MA"/>
<org.eventb.core.variable name="_h" org.eventb.core.identifier="h"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION"/>
<org.eventb.core.event name="_m" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="merged">
<org.eventb.core.refinesEvent name="_r1" org.eventb.core.target="evtP"/>
<org.eventb.core.refinesEvent name="_r2" org.eventb.core.target="evtQ"/>
<org.eventb.core.guard name="_g" org.eventb.core.label="grd" org.eventb.core.predicate="h = 0"/>
<org.eventb.core.witness name="_wp" org.eventb.core.label="p" org.eventb.core.predicate="p = 1"/>
<org.eventb.core.action name="_a" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;
    let r = build(&Project::new(
        "prj",
        vec![xml("MA.bum", ma), xml("MB.bum", mb)],
    ));
    let errors = merge_errors(&r);
    assert_eq!(errors.len(), 1, "{:?}", r.diagnostics);
    assert!(
        errors[0].contains("parameter 'p' type conflict"),
        "{}",
        errors[0]
    );
}

#[test]
fn union_of_abstract_parameters_needs_witnesses() {
    let ma = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_h" org.eventb.core.identifier="h"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="h ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_ih" org.eventb.core.assignment="h ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e1" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evtP">
<org.eventb.core.parameter name="_p1" org.eventb.core.identifier="p"/>
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd" org.eventb.core.predicate="p ∈ ℕ"/>
<org.eventb.core.action name="_a1" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e2" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="evtQ">
<org.eventb.core.parameter name="_q1" org.eventb.core.identifier="q"/>
<org.eventb.core.guard name="_g2" org.eventb.core.label="grd" org.eventb.core.predicate="q ∈ ℕ"/>
<org.eventb.core.action name="_a2" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;
    let mb = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r" org.eventb.core.target="MA"/>
<org.eventb.core.variable name="_h" org.eventb.core.identifier="h"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION"/>
<org.eventb.core.event name="_m" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="merged">
<org.eventb.core.refinesEvent name="_r1" org.eventb.core.target="evtP"/>
<org.eventb.core.refinesEvent name="_r2" org.eventb.core.target="evtQ"/>
<org.eventb.core.guard name="_g" org.eventb.core.label="grd" org.eventb.core.predicate="h = 0"/>
<org.eventb.core.witness name="_wp" org.eventb.core.label="p" org.eventb.core.predicate="p = 1"/>
<org.eventb.core.witness name="_wq" org.eventb.core.label="q" org.eventb.core.predicate="q = 2"/>
<org.eventb.core.action name="_a" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#;
    let r = build(&Project::new(
        "prj",
        vec![xml("MA.bum", ma), xml("MB.bum", mb)],
    ));
    assert!(r.is_ok(), "diagnostics: {:?}", r.diagnostics);
    let view = rossi_build::sc_view::ScView::from_xml(&r.file("MB.bcm").unwrap().contents).unwrap();
    let merged = view.events.get("merged").expect("merged present");
    assert!(merged.accurate, "{:?}", r.diagnostics);
    let witness_labels: Vec<&str> = merged
        .witnesses
        .values()
        .map(|w| w.label.as_str())
        .collect();
    assert!(witness_labels.contains(&"p") && witness_labels.contains(&"q"));
}

#[test]
fn extended_event_cannot_merge() {
    // An extended event inherits its body, so `setBoth` carries no own
    // clauses here; the second target is rejected and the first kept.
    // The readers keep only an extended event's first target, so the
    // second one is added on the AST — the check guards models built
    // through the API.
    let mut mb_component = xml(
        "MB.bum",
        &mb(
            r#"<org.eventb.core.refinesEvent name="_r1" org.eventb.core.target="setHeight"/>"#,
            "true",
        ),
    );
    let rossi::Component::Machine(machine) = &mut mb_component.component else {
        panic!("Expected Machine component");
    };
    machine
        .events
        .iter_mut()
        .find(|e| e.name == "setBoth")
        .unwrap()
        .refines
        .push(rossi::NamedElement::new("setWidth".into()));
    let r = build(&Project::new("prj", vec![xml("MA.bum", MA), mb_component]));
    let errors = merge_errors(&r);
    assert_eq!(errors.len(), 1, "{:?}", r.diagnostics);
    assert!(errors[0].contains("extended"), "{}", errors[0]);
    let view = rossi_build::sc_view::ScView::from_xml(&r.file("MB.bcm").unwrap().contents).unwrap();
    let set_both = view.events.get("setBoth").expect("setBoth kept");
    assert_eq!(set_both.refines_events.len(), 1, "first target kept");
    assert!(!set_both.accurate);
}

#[test]
fn duplicate_target_is_dropped_with_a_warning() {
    let children = r#"<org.eventb.core.refinesEvent name="_r1" org.eventb.core.target="setHeight"/>
<org.eventb.core.refinesEvent name="_r2" org.eventb.core.target="setHeight"/>
<org.eventb.core.guard name="_g" org.eventb.core.label="grd" org.eventb.core.predicate="h = 0"/>
<org.eventb.core.action name="_a1" org.eventb.core.assignment="h ≔ 17" org.eventb.core.label="alfa"/>
<org.eventb.core.action name="_a2" org.eventb.core.assignment="w ≔ 17" org.eventb.core.label="beta"/>"#;
    let r = build(&Project::new(
        "prj",
        vec![xml("MA.bum", MA), xml("MB.bum", &mb(children, "false"))],
    ));
    assert!(
        r.diagnostics.iter().any(|d| {
            d.severity == Severity::Warning && d.message.contains("ambiguous abstract event")
        }),
        "{:?}",
        r.diagnostics
    );
    let view = rossi_build::sc_view::ScView::from_xml(&r.file("MB.bcm").unwrap().contents).unwrap();
    assert_eq!(view.events["setBoth"].refines_events.len(), 1);
}

#[test]
fn explicit_initialisation_target_is_rejected() {
    let children = r#"<org.eventb.core.refinesEvent name="_r1" org.eventb.core.target="INITIALISATION"/>
<org.eventb.core.guard name="_g" org.eventb.core.label="grd" org.eventb.core.predicate="h = 0"/>"#;
    let r = build(&Project::new(
        "prj",
        vec![xml("MA.bum", MA), xml("MB.bum", &mb(children, "false"))],
    ));
    assert!(
        r.diagnostics.iter().any(|d| {
            d.severity == Severity::Error
                && d.message
                    .contains("INITIALISATION cannot be a refinement target")
        }),
        "{:?}",
        r.diagnostics
    );
    let view = rossi_build::sc_view::ScView::from_xml(&r.file("MB.bcm").unwrap().contents).unwrap();
    let set_both = view.events.get("setBoth").expect("event kept");
    assert!(set_both.refines_events.is_empty(), "clause dropped");
}

#[test]
fn merged_abstract_convergence_is_the_weakest() {
    // setHeight is convergent, setWidth ordinary: the merged event may
    // not claim anticipated (stronger than the weakest abstraction).
    let ma = MA.replace(
        r#"name="_sh" org.eventb.core.convergence="0""#,
        r#"name="_sh" org.eventb.core.convergence="1""#,
    );
    let mb_src = mb(SET_BOTH_MERGE, "false").replace(
        r#"name="_sb" org.eventb.core.convergence="0""#,
        r#"name="_sb" org.eventb.core.convergence="2""#,
    );
    let r = build(&Project::new(
        "prj",
        vec![xml("MA.bum", &ma), xml("MB.bum", &mb_src)],
    ));
    let view = rossi_build::sc_view::ScView::from_xml(&r.file("MB.bcm").unwrap().contents).unwrap();
    assert_eq!(
        view.events["setBoth"].convergence.as_deref(),
        Some("0"),
        "downgraded to ordinary: {:?}",
        r.diagnostics
    );
}

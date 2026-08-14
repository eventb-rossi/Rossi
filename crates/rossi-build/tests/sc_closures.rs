//! Typed closure lookups on the checked model: seen-context hoisting,
//! abstract-context closures, refinement ancestry, inherited
//! invariants, and abstract-event resolution.

use rossi_build::{Project, ProjectComponent, build_with_model, sc_model::ScModel};

mod common;
use common::xml;

fn model(name: &str, components: Vec<ProjectComponent>) -> ScModel {
    let (build, model) = build_with_model(&Project::new(name, components));
    assert!(build.is_ok(), "build diagnostics: {:?}", build.diagnostics);
    model
}

mod refinement_chain {
    //! M0 ← M1 ← M2, one invariant and one event each.

    use super::*;

    fn chain() -> ScModel {
        let m0 = xml(
            "M0.bum",
            r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_v0" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i0" org.eventb.core.label="inv0" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init0" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a0" org.eventb.core.assignment="x ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e0" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="E">
<org.eventb.core.guard name="_g0" org.eventb.core.label="grd1" org.eventb.core.predicate="x &gt; 0"/>
<org.eventb.core.action name="_ea0" org.eventb.core.assignment="x ≔ x + 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
        );
        let m1 = xml(
            "M1.bum",
            r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r1" org.eventb.core.target="M0"/>
<org.eventb.core.variable name="_v1" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="x ≥ 0"/>
<org.eventb.core.event name="_init1" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a1" org.eventb.core.assignment="x ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e1" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="E">
<org.eventb.core.refinesEvent name="_re1" org.eventb.core.target="E"/>
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd1" org.eventb.core.predicate="x &gt; 0"/>
<org.eventb.core.action name="_ea1" org.eventb.core.assignment="x ≔ x + 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
        );
        let m2 = xml(
            "M2.bum",
            r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_r2" org.eventb.core.target="M1"/>
<org.eventb.core.variable name="_v2" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_i2" org.eventb.core.label="inv2" org.eventb.core.predicate="x ≤ 100"/>
<org.eventb.core.event name="_init2" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a2" org.eventb.core.assignment="x ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_e2" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="E">
<org.eventb.core.refinesEvent name="_re2" org.eventb.core.target="E"/>
<org.eventb.core.guard name="_g2" org.eventb.core.label="grd1" org.eventb.core.predicate="x &gt; 0"/>
<org.eventb.core.action name="_ea2" org.eventb.core.assignment="x ≔ x + 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
        );
        model("chain", vec![m0, m1, m2])
    }

    #[test]
    fn refined_machine_resolves_the_direct_parent() {
        let model = chain();
        let m2 = &model.machines["M2"];
        assert_eq!(model.refined_machine(m2).unwrap().name(), "M1");
        let m0 = &model.machines["M0"];
        assert!(model.refined_machine(m0).is_none());
    }

    #[test]
    fn inherited_invariants_walk_ancestors_oldest_first() {
        let model = chain();
        let m2 = &model.machines["M2"];
        let rows: Vec<&str> = model
            .inherited_invariants(m2)
            .into_iter()
            .map(|inv| inv.label.as_str())
            .collect();
        assert_eq!(rows, vec!["inv0", "inv1"]);
        assert!(model.inherited_invariants(&model.machines["M0"]).is_empty());
    }

    #[test]
    fn abstract_event_resolves_explicit_and_implicit_refinement() {
        let model = chain();
        let m2 = &model.machines["M2"];
        let e2 = &m2.events_by_label["E"];
        let abstract_events = model.abstract_events(m2, e2);
        let abstract_event = abstract_events.first().expect("E refines M1.E");
        assert_eq!(abstract_event.label, "E");
        assert_eq!(abstract_event.guards[0].label, "grd1");

        // INITIALISATION refines the abstract INITIALISATION implicitly.
        let init = &m2.events_by_label["INITIALISATION"];
        assert!(!model.abstract_events(m2, init).is_empty());

        // The root machine's events refine nothing.
        let m0 = &model.machines["M0"];
        assert!(
            model
                .abstract_events(m0, &m0.events_by_label["E"])
                .is_empty()
        );
    }

    #[test]
    fn event_children_resolve_their_internal_names() {
        let model = chain();
        let m0 = &model.machines["M0"];
        // A fresh build generates the internal names; `'` is the first
        // generated name in an event with no retained identities.
        assert_eq!(
            m0.event_child_internal_name("E", rossi_build::xml_out::tag::SC_GUARD, "grd1"),
            Some("'")
        );
        assert_eq!(
            m0.event_child_internal_name("E", rossi_build::xml_out::tag::SC_GUARD, "missing"),
            None
        );
        assert_eq!(
            m0.event_child_internal_name("missing", rossi_build::xml_out::tag::SC_GUARD, "grd1"),
            None
        );
    }
}

mod diamond_extends {
    //! C0 at the top, C1 and C2 both extend C0, C3 extends C1 and C2.

    use super::*;

    fn context(filename: &str, name_hint: &str, extends: &[&str], axiom: &str) -> ProjectComponent {
        let extends_rows: String = extends
            .iter()
            .enumerate()
            .map(|(i, target)| {
                format!(
                    r#"<org.eventb.core.extendsContext name="_x{name_hint}{i}" org.eventb.core.target="{target}"/>"#
                )
            })
            .collect();
        xml(
            filename,
            &format!(
                r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
{extends_rows}
<org.eventb.core.constant name="_c{name_hint}" org.eventb.core.identifier="k{name_hint}"/>
<org.eventb.core.axiom name="_a{name_hint}" org.eventb.core.label="axm1" org.eventb.core.predicate="{axiom}"/>
</org.eventb.core.contextFile>"#
            ),
        )
    }

    fn diamond() -> ScModel {
        let c0 = context("C0.buc", "0", &[], "k0 ∈ ℤ");
        let c1 = context("C1.buc", "1", &["C0"], "k1 ∈ ℤ");
        let c2 = context("C2.buc", "2", &["C0"], "k2 ∈ ℤ");
        let c3 = context("C3.buc", "3", &["C1", "C2"], "k3 ∈ ℤ");
        let machine = xml(
            "M.bum",
            r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.seesContext name="_s" org.eventb.core.target="C3"/>
</org.eventb.core.machineFile>"#,
        );
        model("diamond", vec![c0, c1, c2, c3, machine])
    }

    #[test]
    fn abstract_contexts_deduplicate_the_shared_ancestor() {
        let model = diamond();
        let c3 = &model.contexts["C3"];
        let names: Vec<&str> = model
            .abstract_contexts(c3)
            .into_iter()
            .map(|c| c.name())
            .collect();
        assert_eq!(names, vec!["C0", "C1", "C2"]);
    }

    #[test]
    fn seen_contexts_hoist_ancestors_before_each_target() {
        let model = diamond();
        let machine = &model.machines["M"];
        let names: Vec<&str> = model
            .seen_contexts(machine)
            .into_iter()
            .map(|c| c.name())
            .collect();
        assert_eq!(names, vec!["C0", "C1", "C2", "C3"]);
    }
}

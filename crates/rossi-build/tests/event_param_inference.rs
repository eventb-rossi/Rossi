//! Event parameters typed only through guard shapes the inference engine
//! must decompose. Rodin parity — each fixture is distilled from a
//! real-world corpus machine:
//!
//! - Group M: a parameter constrained only by `⇒`-consequents, via
//!   `(flag = TRUE ⇒ trigs = {proc}) ∧ (flag = FALSE ⇒ trigs = ∅)`.
//! - Group N: a maplet equated to a function application — `m ↦ t =
//!   msgspace(port)` — decomposing the function's product codomain across
//!   the maplet's leaves.
//! - Group Q: a set-operator equality whose other operand has a known
//!   type, via `vss_set ∩ ma[{tr}] = ∅` against `ma`'s `ℙ(TRAIN × VSS)`
//!   relational-image codomain.

use rossi_build::{Project, ProjectComponent, build, sc_view::ScView};

const IMPLICATION_CTX_BUC: &str = r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.carrierSet name="_set1" org.eventb.core.identifier="PROCESSES"/>
</org.eventb.core.contextFile>
"#;

const IMPLICATION_MACHINE_BUM: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.seesContext name="_s1" org.eventb.core.target="Ctx"/>
<org.eventb.core.variable name="_v1" org.eventb.core.identifier="timeout_trigger"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="timeout_trigger ⊆ PROCESSES"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a0" org.eventb.core.assignment="timeout_trigger ≔ ∅" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_ev_resume" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="resume">
<org.eventb.core.parameter name="_p1" org.eventb.core.identifier="proc"/>
<org.eventb.core.parameter name="_p2" org.eventb.core.identifier="flag"/>
<org.eventb.core.parameter name="_p3" org.eventb.core.identifier="trigs"/>
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd1" org.eventb.core.predicate="proc ∈ PROCESSES"/>
<org.eventb.core.guard name="_g2" org.eventb.core.label="grd2" org.eventb.core.predicate="flag ∈ BOOL"/>
<org.eventb.core.guard name="_g3" org.eventb.core.label="grd49" org.eventb.core.predicate="(flag = TRUE ⇒ trigs = {proc}) ∧ (flag = FALSE ⇒ trigs = ∅)"/>
<org.eventb.core.action name="_a1" org.eventb.core.assignment="timeout_trigger ≔ timeout_trigger ∖ trigs" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>
"#;

const MAPLET_CTX_BUC: &str = r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.carrierSet name="_set1" org.eventb.core.identifier="PORTS"/>
<org.eventb.core.carrierSet name="_set2" org.eventb.core.identifier="MESSAGES"/>
<org.eventb.core.constant name="_c1" org.eventb.core.identifier="msgspace"/>
<org.eventb.core.axiom name="_a1" org.eventb.core.label="axm1" org.eventb.core.predicate="msgspace ∈ PORTS ⇸ MESSAGES × ℤ"/>
</org.eventb.core.contextFile>
"#;

const MAPLET_MACHINE_BUM: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.seesContext name="_s1" org.eventb.core.target="Ctx"/>
<org.eventb.core.variable name="_v1" org.eventb.core.identifier="last"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="last ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a0" org.eventb.core.assignment="last ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_ev_read" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="read_message">
<org.eventb.core.parameter name="_p1" org.eventb.core.identifier="port"/>
<org.eventb.core.parameter name="_p2" org.eventb.core.identifier="m"/>
<org.eventb.core.parameter name="_p3" org.eventb.core.identifier="t"/>
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd1" org.eventb.core.predicate="port ∈ dom(msgspace)"/>
<org.eventb.core.guard name="_g2" org.eventb.core.label="grd2" org.eventb.core.predicate="m ↦ t = msgspace(port)"/>
<org.eventb.core.action name="_a1" org.eventb.core.assignment="last ≔ t" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>
"#;

const SET_OP_CTX_BUC: &str = r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.carrierSet name="_set1" org.eventb.core.identifier="TRAIN"/>
<org.eventb.core.carrierSet name="_set2" org.eventb.core.identifier="VSS"/>
<org.eventb.core.constant name="_c1" org.eventb.core.identifier="ma"/>
<org.eventb.core.axiom name="_a1" org.eventb.core.label="axm1" org.eventb.core.predicate="ma ∈ ℙ(TRAIN × VSS)"/>
</org.eventb.core.contextFile>
"#;

const SET_OP_MACHINE_BUM: &str = r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.seesContext name="_s1" org.eventb.core.target="Ctx"/>
<org.eventb.core.variable name="_v1" org.eventb.core.identifier="last"/>
<org.eventb.core.invariant name="_i1" org.eventb.core.label="inv1" org.eventb.core.predicate="last ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_a0" org.eventb.core.assignment="last ≔ 0" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_ev_extend" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="extend_like">
<org.eventb.core.parameter name="_p1" org.eventb.core.identifier="tr"/>
<org.eventb.core.parameter name="_p2" org.eventb.core.identifier="vss_set"/>
<org.eventb.core.guard name="_g1" org.eventb.core.label="grd1" org.eventb.core.predicate="tr ∈ dom(ma)"/>
<org.eventb.core.guard name="_g2" org.eventb.core.label="grd2" org.eventb.core.predicate="vss_set ∩ ma[{tr}] = ∅"/>
<org.eventb.core.action name="_a1" org.eventb.core.assignment="last ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>
"#;

struct Case {
    name: &'static str,
    ctx_buc: &'static str,
    machine_bum: &'static str,
    event: &'static str,
    expected_params: &'static [(&'static str, &'static str)],
}

#[test]
fn parameter_typed_via_guard_shape() {
    let cases = [
        Case {
            name: "implication_pair_consequent",
            ctx_buc: IMPLICATION_CTX_BUC,
            machine_bum: IMPLICATION_MACHINE_BUM,
            event: "resume",
            expected_params: &[("trigs", "ℙ(PROCESSES)")],
        },
        Case {
            name: "maplet_equality_against_function_application",
            ctx_buc: MAPLET_CTX_BUC,
            machine_bum: MAPLET_MACHINE_BUM,
            event: "read_message",
            expected_params: &[("m", "MESSAGES"), ("t", "ℤ")],
        },
        Case {
            name: "set_op_equality_with_typed_sibling_operand",
            ctx_buc: SET_OP_CTX_BUC,
            machine_bum: SET_OP_MACHINE_BUM,
            event: "extend_like",
            expected_params: &[("tr", "TRAIN"), ("vss_set", "ℙ(VSS)")],
        },
    ];
    for case in cases {
        let name = case.name;
        let project = Project::new(
            "p",
            vec![
                ProjectComponent::from_xml("Ctx.buc", case.ctx_buc).unwrap(),
                ProjectComponent::from_xml("Mch.bum", case.machine_bum).unwrap(),
            ],
        );
        let r = build(&project);
        assert!(r.is_ok(), "{name}: diagnostics: {:?}", r.diagnostics);
        let bcm = r.file("Mch.bcm").expect("Mch.bcm");
        assert!(
            bcm.accurate,
            "{name}: file should remain accurate; diagnostics: {:?}",
            r.diagnostics
        );
        let v = ScView::from_xml(&bcm.contents).unwrap();
        let ev = v
            .events
            .get(case.event)
            .unwrap_or_else(|| panic!("{name}: event {:?} present", case.event));
        assert!(
            ev.accurate,
            "{name}: event should be accurate; diagnostics: {:?}",
            r.diagnostics
        );
        for (param, ty) in case.expected_params {
            assert_eq!(
                ev.parameters.get(*param).map(String::as_str),
                Some(*ty),
                "{name}: {param} should be inferred as {ty}; parameters: {:?}",
                ev.parameters
            );
        }
    }
}

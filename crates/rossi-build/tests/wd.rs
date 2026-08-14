use rossi_build::{Project, ProjectComponent, RuleId, Severity, build_with_model, wd};

fn project(components: Vec<ProjectComponent>) -> Project {
    Project::new("wd", components)
}

fn findings(project: &Project) -> Vec<rossi_build::Diagnostic> {
    let (build, model) = build_with_model(project);
    assert!(build.is_ok(), "build diagnostics: {:?}", build.diagnostics);
    wd::run(project, &model)
}

#[test]
fn reports_every_checked_formula_location_and_omits_trivial_lemmas() {
    let context = ProjectComponent::from_xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.constant name="_n" org.eventb.core.identifier="n"/>
<org.eventb.core.axiom name="_type" org.eventb.core.label="type" org.eventb.core.predicate="n ∈ ℤ"/>
<org.eventb.core.axiom name="_wd" org.eventb.core.label="axm" org.eventb.core.predicate="10 ÷ n &gt; 0"/>
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
<org.eventb.core.invariant name="_wd" org.eventb.core.label="inv" org.eventb.core.predicate="10 ÷ x &gt; 0"/>
<org.eventb.core.variant name="_variant" org.eventb.core.expression="10 ÷ x" org.eventb.core.label="vrn1"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_init_a" org.eventb.core.assignment="x ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_event" org.eventb.core.convergence="1" org.eventb.core.extended="false" org.eventb.core.label="E">
<org.eventb.core.guard name="_guard" org.eventb.core.label="grd" org.eventb.core.predicate="10 ÷ x &gt; 0"/>
<org.eventb.core.action name="_action" org.eventb.core.assignment="x ≔ 10 ÷ x" org.eventb.core.label="act"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    )
    .unwrap();

    let diagnostics = findings(&project(vec![context, machine]));
    let rows: Vec<_> = diagnostics
        .iter()
        .map(|d| (d.origin.as_str(), d.message.as_str()))
        .collect();

    assert_eq!(
        rows,
        vec![
            ("C.axm", "Well-definedness condition: n≠0"),
            ("M.inv", "Well-definedness condition: x≠0"),
            ("M.vrn1", "Well-definedness condition: x≠0"),
            ("M.E/grd", "Well-definedness condition: x≠0"),
            ("M.E/act", "Well-definedness condition: x≠0"),
        ]
    );
    assert!(
        diagnostics.iter().all(|d| {
            d.severity == Severity::Info && d.rule_id == Some(RuleId::WellDefinedness)
        })
    );
}

#[test]
fn reports_each_variant_under_its_own_label() {
    let machine = ProjectComponent::from_xml(
        "M.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_type" org.eventb.core.label="type" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.variant name="_first" org.eventb.core.expression="20 ÷ (x + 1)" org.eventb.core.label="v1"/>
<org.eventb.core.variant name="_last" org.eventb.core.expression="10 ÷ x" org.eventb.core.label="v2"/>
</org.eventb.core.machineFile>"#,
    )
    .unwrap();

    let diagnostics = findings(&project(vec![machine]));

    let rows: Vec<(&str, &str)> = diagnostics
        .iter()
        .map(|d| (d.origin.as_str(), d.message.as_str()))
        .collect();
    assert_eq!(
        rows,
        vec![
            ("M.v1", "Well-definedness condition: x+1≠0"),
            ("M.v2", "Well-definedness condition: x≠0"),
        ]
    );
}

#[test]
fn reports_witnesses_and_does_not_duplicate_inherited_actions() {
    let abstract_machine = ProjectComponent::from_xml(
        "M0.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_type" org.eventb.core.label="type" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="INITIALISATION">
<org.eventb.core.action name="_init_a" org.eventb.core.assignment="x ≔ 1" org.eventb.core.label="act1"/>
</org.eventb.core.event>
<org.eventb.core.event name="_event" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="E">
<org.eventb.core.parameter name="_p" org.eventb.core.identifier="p"/>
<org.eventb.core.guard name="_type_p" org.eventb.core.label="type" org.eventb.core.predicate="p ∈ ℤ"/>
</org.eventb.core.event>
<org.eventb.core.event name="_inherited_event" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="F">
<org.eventb.core.action name="_action" org.eventb.core.assignment="x ≔ 10 ÷ x" org.eventb.core.label="inherited"/>
</org.eventb.core.event>
</org.eventb.core.machineFile>"#,
    )
    .unwrap();
    let concrete_machine = ProjectComponent::from_xml(
        "M1.bum",
        r#"<?xml version="1.0"?>
<org.eventb.core.machineFile version="5" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.refinesMachine name="_ref" org.eventb.core.target="M0"/>
<org.eventb.core.variable name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.invariant name="_type" org.eventb.core.label="type" org.eventb.core.predicate="x ∈ ℤ"/>
<org.eventb.core.event name="_init" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="INITIALISATION"/>
<org.eventb.core.event name="_event" org.eventb.core.convergence="0" org.eventb.core.extended="false" org.eventb.core.label="E">
<org.eventb.core.refinesEvent name="_ref_event" org.eventb.core.target="E"/>
<org.eventb.core.witness name="_witness" org.eventb.core.label="p" org.eventb.core.predicate="p = 10 ÷ x"/>
</org.eventb.core.event>
<org.eventb.core.event name="_inherited_event" org.eventb.core.convergence="0" org.eventb.core.extended="true" org.eventb.core.label="F"/>
</org.eventb.core.machineFile>"#,
    )
    .unwrap();

    let diagnostics = findings(&project(vec![abstract_machine, concrete_machine]));
    let origins: Vec<_> = diagnostics.iter().map(|d| d.origin.as_str()).collect();

    assert_eq!(origins, vec!["M0.F/inherited", "M1.E/p"]);
}

#[test]
fn uses_the_source_formula_span() {
    let source = concat!(
        "MACHINE M\n",
        "VARIABLES\n    x\n",
        "INVARIANTS\n",
        "    @type x ∈ ℤ\n",
        "    @wd 10 ÷ x > 0\n",
        "END\n",
    );
    let components = ProjectComponent::from_eventb("M.eventb", source).unwrap();
    let diagnostics = findings(&project(components));
    let diagnostic = diagnostics
        .iter()
        .find(|d| d.origin == "M.wd")
        .expect("WD diagnostic");
    let span = diagnostic.span.expect("text formula carries a span");

    assert_eq!(source[span.start..span.end].trim_end(), "10 ÷ x > 0");
}

#[test]
fn rendering_omits_source_ascriptions_and_bound_declaration_annotations() {
    let context = ProjectComponent::from_xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.axiom name="_wd" org.eventb.core.label="axm" org.eventb.core.predicate="∀x⦂ℤ· 1 ÷ (x ⦂ ℤ) &gt; 0"/>
</org.eventb.core.contextFile>"#,
    )
    .unwrap();

    let diagnostics = findings(&project(vec![context]));

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].message, "Well-definedness condition: ∀x·x≠0");
}

#[test]
fn rendering_spaces_cartesian_products_like_formula_to_string() {
    let context = ProjectComponent::from_xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.carrierSet name="_s" org.eventb.core.identifier="S"/>
<org.eventb.core.carrierSet name="_t" org.eventb.core.identifier="T"/>
<org.eventb.core.constant name="_x" org.eventb.core.identifier="x"/>
<org.eventb.core.constant name="_f" org.eventb.core.identifier="f"/>
<org.eventb.core.axiom name="_type_x" org.eventb.core.label="type_x" org.eventb.core.predicate="x ∈ S × T"/>
<org.eventb.core.axiom name="_type_f" org.eventb.core.label="type_f" org.eventb.core.predicate="f ∈ S × T ⇸ S"/>
<org.eventb.core.axiom name="_wd" org.eventb.core.label="axm" org.eventb.core.predicate="f(x) ∈ S"/>
</org.eventb.core.contextFile>"#,
    )
    .unwrap();

    let diagnostics = findings(&project(vec![context]));

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "Well-definedness condition: x∈dom(f)∧f∈S × T ⇸ S"
    );
}

#[test]
fn rendering_spaces_comprehension_bars_like_formula_to_string() {
    let context = ProjectComponent::from_xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.axiom name="_wd" org.eventb.core.label="axm" org.eventb.core.predicate="card({x·x∈ℤ∣x}) &gt; 0"/>
</org.eventb.core.contextFile>"#,
    )
    .unwrap();

    let diagnostics = findings(&project(vec![context]));

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "Well-definedness condition: finite({x·x∈ℤ ∣ x})"
    );
}

#[test]
fn rendering_compacts_relational_composition_like_formula_to_string() {
    let context = ProjectComponent::from_xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.carrierSet name="_s" org.eventb.core.identifier="S"/>
<org.eventb.core.constant name="_r" org.eventb.core.identifier="r"/>
<org.eventb.core.constant name="_t" org.eventb.core.identifier="t"/>
<org.eventb.core.constant name="_f" org.eventb.core.identifier="f"/>
<org.eventb.core.axiom name="_type_r" org.eventb.core.label="type_r" org.eventb.core.predicate="r ∈ S ↔ S"/>
<org.eventb.core.axiom name="_type_t" org.eventb.core.label="type_t" org.eventb.core.predicate="t ∈ S ↔ S"/>
<org.eventb.core.axiom name="_type_f" org.eventb.core.label="type_f" org.eventb.core.predicate="f ∈ (S ↔ S) ⇸ S"/>
<org.eventb.core.axiom name="_wd" org.eventb.core.label="axm" org.eventb.core.predicate="f(r;t) ∈ S"/>
</org.eventb.core.contextFile>"#,
    )
    .unwrap();

    let diagnostics = findings(&project(vec![context]));

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "Well-definedness condition: r;t∈dom(f)∧f∈ℙ(S × S) ⇸ S"
    );
}

#[test]
fn rendering_uses_mathematical_minus_like_formula_to_string() {
    let context = ProjectComponent::from_xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.axiom name="_wd" org.eventb.core.label="axm" org.eventb.core.predicate="card({−1}) &gt; 0"/>
</org.eventb.core.contextFile>"#,
    )
    .unwrap();

    let diagnostics = findings(&project(vec![context]));

    assert_eq!(diagnostics.len(), 1);
    assert_eq!(
        diagnostics[0].message,
        "Well-definedness condition: finite({−1})"
    );
}

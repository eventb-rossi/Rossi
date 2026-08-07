//! End-to-end test: binary-search/C0.buc has constants `n`, `f`, `v` and
//! four axioms. We should emit a .bcc whose axioms and constants are
//! semantically equivalent to Rodin's, with inferred types for each
//! constant.

use rossi_build::{Project, ProjectComponent, build};

const C0_BUC: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.contextFile org.eventb.core.configuration="org.eventb.core.fwd" version="3">
    <org.eventb.core.constant name="'" org.eventb.core.identifier="n"/>
    <org.eventb.core.constant name="*" org.eventb.core.identifier="f"/>
    <org.eventb.core.constant name="(" org.eventb.core.identifier="v"/>
    <org.eventb.core.axiom name=")" org.eventb.core.label="axm1" org.eventb.core.predicate="n ∈ ℕ"/>
    <org.eventb.core.axiom name="+" org.eventb.core.label="axm2" org.eventb.core.predicate="f ∈ (0 ‥ n − 1) → ℤ"/>
    <org.eventb.core.axiom name="," org.eventb.core.label="axm3" org.eventb.core.predicate="v ∈ ran(f)"/>
    <org.eventb.core.axiom name="-" org.eventb.core.label="axm4" org.eventb.core.predicate="∀x, y · x ∈ dom(f) ∧ y ∈ dom(f) ∧ x ≤ y ⇒ f(x) ≤ f(y)"/>
</org.eventb.core.contextFile>
"#;

fn make_project() -> Project {
    let pc = ProjectComponent::from_xml("C0.buc", C0_BUC).unwrap();
    Project::new("binary-search", vec![pc])
}

#[test]
fn emits_a_bcc_file() {
    let result = build(&make_project());
    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].filename, "C0.bcc");
}

#[test]
fn integer_constant_gets_integer_type() {
    let result = build(&make_project());
    let xml = &result.files[0].contents;
    // n : ℤ (inferred from n ∈ ℕ, since ℕ : ℙ(ℤ))
    assert!(
        xml.contains(r#"<org.eventb.core.scConstant name="n""#)
            && xml.contains(r#"org.eventb.core.type="ℤ""#),
        "n should get type ℤ, got:\n{xml}"
    );
}

#[test]
fn integer_relation_constant_gets_pow_int_times_int() {
    let result = build(&make_project());
    let xml = &result.files[0].contents;
    // f : ℙ(ℤ×ℤ) (inferred from f ∈ (0‥n−1) → ℤ)
    assert!(
        xml.contains(r#"name="f""#) && xml.contains("ℙ(ℤ×ℤ)"),
        "f should get type ℙ(ℤ×ℤ), got:\n{xml}"
    );
}

#[test]
fn constants_are_sorted_alphabetically() {
    let result = build(&make_project());
    let xml = &result.files[0].contents;
    let idx_f = xml.find(r#"<org.eventb.core.scConstant name="f""#).unwrap();
    let idx_n = xml.find(r#"<org.eventb.core.scConstant name="n""#).unwrap();
    let idx_v = xml.find(r#"<org.eventb.core.scConstant name="v""#).unwrap();
    assert!(idx_f < idx_n && idx_n < idx_v);
}

#[test]
fn axioms_appear_before_constants() {
    let result = build(&make_project());
    let xml = &result.files[0].contents;
    let first_axiom = xml.find("<org.eventb.core.scAxiom").unwrap();
    let first_constant = xml.find("<org.eventb.core.scConstant").unwrap();
    assert!(
        first_axiom < first_constant,
        "expected scAxiom elements before scConstant elements"
    );
}

#[test]
fn predicates_are_canonical_unicode() {
    let result = build(&make_project());
    let xml = &result.files[0].contents;
    // Simple membership + function-application axioms: byte-exact with
    // Rodin. axm2 pins our current canonical emission (parenthesized
    // domain dropped); re-parseability of these shapes is covered by
    // tests/properties.rs.
    for expected in [
        r#"org.eventb.core.predicate="n∈ℕ""#,
        r#"org.eventb.core.predicate="f∈0 ‥ n − 1 → ℤ""#,
        r#"org.eventb.core.predicate="v∈ran(f)""#,
    ] {
        assert!(
            xml.contains(expected),
            "expected {expected} in output:\n{xml}"
        );
    }
    // Quantified axm4 — binder type ascriptions (`⦂ℤ`) are now stamped
    // on by the enrich pass, matching Rodin byte-for-byte.
    assert!(
        xml.contains(r#"∀x⦂ℤ,y⦂ℤ·x∈dom(f)∧y∈dom(f)∧x≤y⇒f(x)≤f(y)"#),
        "axm4 differs from Rodin in unexpected way:\n{xml}"
    );
}

#[test]
fn accurate_is_true_when_all_constants_are_inferred() {
    let result = build(&make_project());
    let xml = &result.files[0].contents;
    assert!(xml.contains("org.eventb.core.accurate=\"true\""));
    assert!(result.files[0].accurate);
    assert!(result.is_ok(), "diagnostics: {:?}", result.diagnostics);
}

/// Group S: a context axiom of the shape
/// `c = (λ x · x = ∅ ∣ 0) ∪ (λ x⦂T · …)` must type the first
/// lambda's binder by lifting the function type from the typed
/// sibling across the `∪`. Rodin parity — verified against a
/// real-world corpus context whose constant is
/// `ℙ(ℙ(ℤ×ℤ)×ℤ)` and both lambdas end up with `x⦂ℙ(ℤ×ℤ)` binders.
const CTX_BUC: &str = r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.constant name="_c1" org.eventb.core.identifier="integral"/>
<org.eventb.core.axiom name="_a1" org.eventb.core.label="f_integral" org.eventb.core.predicate="integral = (λ x · x = ∅ ∣ 0) ∪ (λ x⦂ℙ(ℤ×ℤ) · x ∈ ℤ ⇸ ℤ ∣ 1)"/>
</org.eventb.core.contextFile>
"#;

fn project() -> Project {
    Project::new(
        "s",
        vec![ProjectComponent::from_xml("Ctx.buc", CTX_BUC).unwrap()],
    )
}

#[test]
fn lambda_binder_typed_via_typed_sibling_across_union() {
    let r = build(&project());
    let bcc = r.file("Ctx.bcc").expect("Ctx.bcc");
    assert!(
        bcc.accurate,
        "context file should be accurate; diagnostics: {:?}",
        r.diagnostics
    );
    assert!(r.is_ok(), "diagnostics: {:?}", r.diagnostics);
    // Both lambda binders must carry the lifted `⦂ℙ(ℤ×ℤ)` ascription in
    // the emitted predicate — the source supplies only one of them.
    let marker = "org.eventb.core.label=\"f_integral\" org.eventb.core.predicate=\"";
    let start = bcc.contents.find(marker).expect("f_integral axiom present") + marker.len();
    let end = start + bcc.contents[start..].find('"').unwrap();
    let predicate = &bcc.contents[start..end];
    assert_eq!(
        predicate.matches("⦂ℙ(ℤ×ℤ)").count(),
        2,
        "both lambda binders should carry the lifted ascription: {predicate}"
    );
}

//! #24 — property tests for the normalization / inference layer.
//!
//! These are regression insurance: they assert laws that must hold for
//! every input, and they catch classes of bugs that hand-written
//! fixtures miss. Run with `cargo test -p rossi-build --test properties`.
//!
//! Laws covered:
//!
//! 1. **Idempotence**: `canonical(parse(canonical(parse(s))))
//!                     == canonical(parse(s))`.
//! 2. **Parseability**: every canonical form parses back.
//! 3. **AST round-trip** (modulo type ascriptions):
//!    `strip(parse(canonical(p))) == strip(p)`.
//! 4. **Inference monotonicity**: if a context build types constant `c`
//!    from axioms `A`, a build over any superset `A ∪ B` still types
//!    `c` identically — adding axioms never "untypes" a constant.
//! 5. **Scope stack**: push/insert/pop restores outer env regardless
//!    of how many layers.

use proptest::prelude::*;
use rossi::{parse_action_str, parse_predicate_str};
use rossi_build::normalize::{canonical_action, canonical_predicate};
use rossi_build::sc_view::{ScView, strip_type_ascriptions_action, strip_type_ascriptions_pred};
use rossi_build::type_env::TypeEnv;
use rossi_build::types::Type;
use rossi_build::{Project, ProjectComponent, build};

// ---------------------------------------------------------------------
// Strategies — hand-curated string samples instead of grammar-walking.
// Covers the predicate/action shapes that actually appear in the corpus.
// ---------------------------------------------------------------------

fn predicate_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("n ∈ ℕ".to_string()),
        Just("register ⊆ USERS".to_string()),
        Just("x ∈ dom(f)".to_string()),
        Just("f(x) ≤ f(y)".to_string()),
        Just("x ∉ ran(f)".to_string()),
        Just("a ↦ b ∈ rel".to_string()),
        Just("x ∈ S ∧ y ∈ T".to_string()),
        Just("p ∈ dom(m) ⇒ m(p) ∈ ran(m)".to_string()),
        Just("∀x · x ∈ S ⇒ x ∈ T".to_string()),
        Just("∃y · y ∈ S ∧ y ≠ z".to_string()),
        Just("¬(x = y)".to_string()),
        Just("card(S) > 0".to_string()),
        Just("x ∈ S ∩ T".to_string()),
        Just("r ⊆ S × T".to_string()),
        Just("f ∈ S → T".to_string()),
        Just("f ∈ (0 ‥ n − 1) → ℤ".to_string()),
        Just("∀x, y · x ∈ dom(f) ∧ y ∈ dom(f) ∧ x ≤ y ⇒ f(x) ≤ f(y)".to_string()),
    ]
}

fn action_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("x ≔ 1".to_string()),
        Just("x ≔ x + 1".to_string()),
        Just("register ≔ register ∪ {u}".to_string()),
        Just("register ≔ register ∖ {u}".to_string()),
        Just("x, y ≔ y, x".to_string()),
        Just("x :∈ S".to_string()),
        Just("x :∣ x' > x".to_string()),
    ]
}

// ---------------------------------------------------------------------
// Properties
// ---------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// `canonical_predicate` is idempotent: applying it twice changes
    /// nothing. Formally, for any valid predicate string `s`:
    ///   let p1 = parse(s); let c1 = canonical(p1);
    ///   let p2 = parse(c1); let c2 = canonical(p2);
    ///   c1 == c2
    #[test]
    fn canonical_predicate_is_idempotent(s in predicate_strategy()) {
        let p1 = parse_predicate_str(&s).expect("strategy yields parseable predicates");
        let c1 = canonical_predicate(&p1);
        let p2 = parse_predicate_str(&c1).expect("canonical form must re-parse");
        let c2 = canonical_predicate(&p2);
        prop_assert_eq!(c1, c2);
    }

    /// Every canonical predicate string re-parses cleanly. This is the
    /// guarantee that our Rodin-canonical output never produces text
    /// our own parser refuses.
    #[test]
    fn canonical_predicate_reparseable(s in predicate_strategy()) {
        let p = parse_predicate_str(&s).unwrap();
        let c = canonical_predicate(&p);
        prop_assert!(
            parse_predicate_str(&c).is_ok(),
            "canonical form did not re-parse: {c:?}"
        );
    }

    /// AST round-trip modulo type ascriptions: `strip(parse(canonical(p))) == strip(p)`.
    /// The strip eats the `⦂T` annotations Rodin adds during type-check
    /// so predicates of the form `∀x·P` and `∀x⦂ℤ·P` compare equal.
    #[test]
    fn canonical_predicate_preserves_ast(s in predicate_strategy()) {
        let p = parse_predicate_str(&s).unwrap();
        let c = canonical_predicate(&p);
        let round = parse_predicate_str(&c).unwrap();
        prop_assert_eq!(
            strip_type_ascriptions_pred(round),
            strip_type_ascriptions_pred(p)
        );
    }

    /// Same three laws for actions.
    #[test]
    fn canonical_action_is_idempotent(s in action_strategy()) {
        let a1 = parse_action_str(&s).unwrap();
        let c1 = canonical_action(&a1);
        let a2 = parse_action_str(&c1).unwrap();
        let c2 = canonical_action(&a2);
        prop_assert_eq!(c1, c2);
    }

    #[test]
    fn canonical_action_reparseable(s in action_strategy()) {
        let a = parse_action_str(&s).unwrap();
        let c = canonical_action(&a);
        prop_assert!(parse_action_str(&c).is_ok(), "action canonical did not re-parse: {c:?}");
    }

    #[test]
    fn canonical_action_preserves_ast(s in action_strategy()) {
        let a = parse_action_str(&s).unwrap();
        let c = canonical_action(&a);
        let round = parse_action_str(&c).unwrap();
        prop_assert_eq!(
            strip_type_ascriptions_action(round),
            strip_type_ascriptions_action(a)
        );
    }

    /// Strip is idempotent on predicates.
    #[test]
    fn strip_predicate_is_idempotent(s in predicate_strategy()) {
        let p = parse_predicate_str(&s).unwrap();
        let once = strip_type_ascriptions_pred(p);
        let twice = strip_type_ascriptions_pred(once.clone());
        prop_assert_eq!(once, twice);
    }

    /// Strip is idempotent on actions.
    #[test]
    fn strip_action_is_idempotent(s in action_strategy()) {
        let a = parse_action_str(&s).unwrap();
        let once = strip_type_ascriptions_action(a);
        let twice = strip_type_ascriptions_action(once.clone());
        prop_assert_eq!(once, twice);
    }
}

// ---------------------------------------------------------------------
// Inference monotonicity.
//
// Strategy: fabricate a context with a carrier set, constants, and a
// handful of typing axioms; build it. Then re-build with extra
// (possibly unrelated) axioms appended. The set of typed constants in
// the emitted .bcc must not shrink, and their types must not change.
// ---------------------------------------------------------------------

fn axiom_string_strategy() -> impl Strategy<Value = String> {
    prop_oneof![
        Just("a ∈ USERS".to_string()),
        Just("b ⊆ USERS".to_string()),
        Just("n = 42".to_string()),
        Just("S = {1, 2, 3}".to_string()),
        Just("partition(USERS, {a}, {b})".to_string()),
        Just("r ∈ USERS ↔ USERS".to_string()),
        // Intentionally unrelated axioms that shouldn't type anything.
        Just("TRUE = TRUE".to_string()),
    ]
}

/// A context over carrier set USERS and the strategy's constants, with
/// one labeled axiom per entry.
fn context_component(axioms: &[String]) -> ProjectComponent {
    let mut xml = String::from(
        r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.contextFile org.eventb.core.configuration="org.eventb.core.fwd" version="3">
    <org.eventb.core.carrierSet name="s0" org.eventb.core.identifier="USERS"/>
"#,
    );
    for (i, constant) in ["a", "b", "n", "S", "r"].iter().enumerate() {
        xml.push_str(&format!(
            "    <org.eventb.core.constant name=\"c{i}\" org.eventb.core.identifier=\"{constant}\"/>\n"
        ));
    }
    for (i, axiom) in axioms.iter().enumerate() {
        xml.push_str(&format!(
            "    <org.eventb.core.axiom name=\"x{i}\" org.eventb.core.label=\"axm{i}\" org.eventb.core.predicate=\"{axiom}\"/>\n"
        ));
    }
    xml.push_str("</org.eventb.core.contextFile>\n");
    ProjectComponent::from_xml("C0.buc", &xml).expect("fabricated context parses")
}

/// The `constant name -> type` attribute map of the built context.
fn built_constant_types(axioms: &[String]) -> std::collections::BTreeMap<String, String> {
    let result = build(&Project::new("prop", vec![context_component(axioms)]));
    let bcc = &result.files[0].contents;
    let view = ScView::from_xml(bcc).expect("emitted .bcc parses");
    view.constants
        .into_iter()
        .map(|(name, row)| (name, row.type_str))
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(60))]

    #[test]
    fn constant_typing_is_monotone(
        core_axioms in proptest::collection::vec(axiom_string_strategy(), 1..6),
        extra_axioms in proptest::collection::vec(axiom_string_strategy(), 0..4),
    ) {
        let superset: Vec<String> = core_axioms
            .iter()
            .chain(extra_axioms.iter())
            .cloned()
            .collect();

        let small = built_constant_types(&core_axioms);
        let big = built_constant_types(&superset);

        // Every constant typed with the core axiom set must still be
        // typed with the superset — and with the same type.
        for (name, ty_small) in &small {
            let ty_big = big.get(name);
            prop_assert_eq!(
                Some(ty_small),
                ty_big,
                "constant {} was typed as {:?} with core axioms but {:?} with superset",
                name,
                ty_small,
                ty_big
            );
        }
    }
}

// ---------------------------------------------------------------------
// TypeEnv scope stack: deeply-nested push/pop restores faithfully.
// ---------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    /// Opening N scopes, inserting one name per scope, and popping N
    /// times restores the exact outer env that was present before the
    /// first push.
    #[test]
    fn scope_stack_restores_after_n_pushes(n in 0usize..10usize) {
        let mut env = TypeEnv::new();
        env.insert("x", Type::Integer);
        let snapshot: Vec<(String, Type)> = env
            .iter()
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect();

        for i in 0..n {
            env.push_scope();
            env.insert("x", Type::GivenSet(format!("S{i}")));
            env.insert(format!("y{i}"), Type::Boolean);
        }
        for _ in 0..n {
            env.pop_scope();
        }

        // After all pops, env must be exactly the snapshot.
        let after: Vec<(String, Type)> = env
            .iter()
            .map(|(k, v)| (k.to_string(), v.clone()))
            .collect();
        prop_assert_eq!(after, snapshot);
    }
}

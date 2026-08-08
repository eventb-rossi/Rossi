//! Differential oracle for the lowering: a parsed formula must print
//! byte-identically through the legacy tree and through its lowered
//! formula-model equivalent, in every printer mode.

use rossi::formula::lower::{lower_action, lower_expression, lower_predicate};
use rossi::{
    Component, FormulaSpacing, PrettyPrinter, parse_action_str, parse_expression_str,
    parse_predicate_str,
};

fn printers() -> Vec<PrettyPrinter> {
    let readable_unicode = PrettyPrinter::new();
    let readable_ascii = PrettyPrinter::ascii();
    let canonical = PrettyPrinter::rodin_canonical();
    let mut canonical_ascii = PrettyPrinter::ascii();
    canonical_ascii.formula_spacing = FormulaSpacing::RodinCanonical;
    vec![readable_unicode, readable_ascii, canonical, canonical_ascii]
}

#[track_caller]
fn check_predicate(source: &str) {
    let legacy = parse_predicate_str(source).expect(source);
    let lowered = lower_predicate(&legacy);
    for printer in printers() {
        assert_eq!(
            printer.print_formula_predicate(&lowered),
            printer.print_predicate(&legacy),
            "predicate {source:?}"
        );
    }
}

#[track_caller]
fn check_expression(source: &str) {
    let legacy = parse_expression_str(source).expect(source);
    let lowered = lower_expression(&legacy);
    for printer in printers() {
        assert_eq!(
            printer.print_formula_expression(&lowered),
            printer.print_expression(&legacy),
            "expression {source:?}"
        );
    }
}

#[track_caller]
fn check_action(source: &str) {
    let legacy = parse_action_str(source).expect(source);
    let Some(lowered) = lower_action(&legacy) else {
        assert_eq!(source.trim(), "skip");
        return;
    };
    for printer in printers() {
        assert_eq!(
            printer.print_formula_assignment(&lowered),
            printer.print_action(&legacy),
            "action {source:?}"
        );
    }
}

#[test]
fn operators_round_trip() {
    for source in [
        "x = 1",
        "a + b + 3 ∗ c = d",
        "a − b − c = a ÷ (b mod c) ^ d",
        "s ∪ t ∪ u ⊆ s ∩ t",
        "s ∖ t ⊂ u",
        "a ↦ b ↦ c ∈ r",
        "x ∈ 1 ‥ 9",
        "f(x) = r[s]",
        "(f ∪ g)(x) = (p ; q ; r)[s]",
        "f∼(y) ∈ dom(f) ∪ ran(f)",
        "card(s) + min(s) + max(s) = 3",
        "union(ss) = inter(ss)",
        "s ◁ f ⩥ t = f ⩤ u",
        "f ⊗ g ∈ A ⇸ B ∥ C",
        "r ∈ A ↔ B ∧ f ∈ A → B ∧ g ∈ A ⤔ B",
        "x ∈ ℕ ∧ y ∈ ℕ1 ∧ z ∈ ℤ ∧ b ∈ BOOL",
        "succ(pred(x)) = x ∧ prj1(p) = prj2(q) ∧ id(v) = v",
        "bool(x = 1) = TRUE ∧ b ≠ FALSE",
        "−(x) < 0 ∨ ¬(x ≥ 1)",
        "finite(s) ∧ partition(s, a, b)",
        "custom(x, y) ∧ x > 0",
        "x ∈ ℕ ⦂ ℤ",
        "∅ ⦂ ℙ(A × B) = c",
        "{1, 2, 3} = s",
    ] {
        check_predicate(source);
    }
}

#[test]
fn binders_round_trip() {
    for source in [
        "∀x·x > 0",
        "∀x, y·x = y",
        "∀x⦂ℤ, y⦂A × B·x ∈ ℕ ∧ y ∈ c",
        "∃x·x ∈ s ∧ (∀y·y ∈ x)",
        "∀x·(∃x·x = 1) ∧ x = 2",
        "∀x·x ∈ s ⇒ (∀y·y ∈ x ⇔ y ∈ t)",
    ] {
        check_predicate(source);
    }
}

#[test]
fn comprehensions_round_trip() {
    for source in [
        "{x·x ∈ s∣x + 1} = t",
        "{x, y·x ↦ y ∈ r∣x + y} = t",
        "{x∣x ∈ s} = t",
        "{x, y∣x ↦ y ∈ r} = t",
        "{x + 1∣x ∈ s} = t",
        "{f(z)∣z ∈ s} = t",
        "(λ x·x ∈ s∣x + 1) = f",
        "(λ x ↦ y·x < y∣x + y) = f",
        "(λ x ↦ (y ↦ z)·x < y∣x + z) = f",
        "(⋃ x·x ∈ s∣{x}) = t",
        "(⋂ x⦂ℙ(A)·x ⊆ s∣x) = t",
        "s = {x∣x ∈ {y∣y ∈ t}}",
    ] {
        check_predicate(source);
    }
}

#[test]
fn actions_round_trip() {
    for source in [
        "x ≔ 1",
        "x, y ≔ y, x",
        "x :∈ s ∪ t",
        "x :∣ x' = x + 1",
        "x, y :∣ x' = y ∧ y' = x",
        "f(a) ≔ b",
        "skip",
    ] {
        check_action(source);
    }
}

#[test]
fn expressions_round_trip() {
    for source in [
        "a + b",
        "(a ↦ b) ↦ c",
        "{x·x > 0∣x ∗ x}",
        "f ⇸ g",
        "ℙ(A ∪ B)",
        "A ⦂ ℙ(B)",
    ] {
        check_expression(source);
    }
}

/// Every formula of every example model prints identically through
/// both trees.
#[test]
fn example_models_round_trip() {
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples");
    let mut checked = 0usize;
    for entry in std::fs::read_dir(&dir).expect("examples directory") {
        let path = entry.expect("directory entry").path();
        if path.extension().and_then(|e| e.to_str()) != Some("eventb") {
            continue;
        }
        let source = std::fs::read_to_string(&path).expect("readable example");
        let components = rossi::parse_components(&source).expect("example parses");
        for component in &components {
            checked += check_component(component);
        }
    }
    assert!(checked > 50, "expected a real corpus, checked {checked}");
}

/// Lowers and compares every formula of a component; returns how many.
fn check_component(component: &Component) -> usize {
    let mut checked = 0;
    let printers = printers();
    let check_pred = |pred: &rossi::Predicate| {
        let lowered = lower_predicate(pred);
        for printer in &printers {
            assert_eq!(
                printer.print_formula_predicate(&lowered),
                printer.print_predicate(pred),
            );
        }
    };
    match component {
        Component::Context(context) => {
            for axiom in &context.axioms {
                check_pred(&axiom.predicate);
                checked += 1;
            }
        }
        Component::Machine(machine) => {
            for invariant in &machine.invariants {
                check_pred(&invariant.predicate);
                checked += 1;
            }
            if let Some(variant) = &machine.variant {
                let lowered = lower_expression(variant);
                for printer in &printers {
                    assert_eq!(
                        printer.print_formula_expression(&lowered),
                        printer.print_expression(variant),
                    );
                }
                checked += 1;
            }
            let check_action_ast = |action: &rossi::Action| {
                if let Some(lowered) = lower_action(action) {
                    for printer in &printers {
                        assert_eq!(
                            printer.print_formula_assignment(&lowered),
                            printer.print_action(action),
                        );
                    }
                }
            };
            if let Some(init) = &machine.initialisation {
                for action in &init.actions {
                    check_action_ast(&action.action);
                    checked += 1;
                }
            }
            for event in &machine.events {
                for guard in &event.guards {
                    check_pred(&guard.predicate);
                    checked += 1;
                }
                for witness in &event.witnesses {
                    check_pred(&witness.predicate);
                    checked += 1;
                }
                for action in &event.actions {
                    check_action_ast(&action.action);
                    checked += 1;
                }
            }
        }
    }
    checked
}

//! Rodin-canonical formula formatting.
//!
//! Rodin's `.bcc`/`.bcm` attribute values use tighter spacing than readable
//! Event-B text. [`PrettyPrinter`] emits that representation directly from
//! the AST; the typed renderings add the type annotations Rodin's static
//! checker introduces (bound-declaration ascriptions, typed empty sets).

use rossi::formula;
use rossi::pretty::PrettyPrinter;
use rossi::{Action, Expression, Predicate};

/// Canonicalise a predicate to Rodin's tight form.
pub fn canonical_predicate(p: &Predicate) -> String {
    PrettyPrinter::rodin_canonical().print_predicate(p)
}

/// Canonicalise a typed predicate: the tight form with every bound
/// declaration carrying its solved type.
pub fn canonical_typed_predicate(p: &formula::Predicate) -> String {
    typed_canonical_printer().print_formula_predicate(p)
}

/// See [`canonical_typed_predicate`].
pub fn canonical_typed_expression(e: &formula::Expression) -> String {
    typed_canonical_printer().print_formula_expression(e)
}

/// Canonicalise a typed assignment, ascribing any bare empty-set value
/// with its solved type (`x ≔ ∅` serialises as `x ≔ ∅ ⦂ ℙ(T)`).
pub fn canonical_typed_assignment(a: &formula::Assignment) -> String {
    typed_canonical_printer().print_formula_assignment(&ascribe_empty_set_values(a))
}

fn typed_canonical_printer() -> PrettyPrinter {
    PrettyPrinter::rodin_canonical().with_typed_decls(true)
}

fn ascribe_empty_set_values(a: &formula::Assignment) -> formula::Assignment {
    let formula::AssignmentKind::BecomesEqualTo { idents, values } = a.kind() else {
        return a.clone();
    };
    let is_bare_empty_set = |value: &formula::Expression| {
        matches!(
            value.kind(),
            formula::ExpressionKind::Atomic(formula::tag::AtomicOp::EmptySet)
        )
    };
    if !values.iter().any(is_bare_empty_set) {
        return a.clone();
    }
    let ff = a.factory().clone();
    let values = values
        .iter()
        .map(|value| match value.ty() {
            Some(ty) if is_bare_empty_set(value) => {
                ff.ascription(value.clone(), ty.to_expression(&ff), None)
            }
            _ => value.clone(),
        })
        .collect();
    ff.becomes_equal_to(idents.clone(), values, None)
}

/// Canonicalise an expression to Rodin's tight form.
pub fn canonical_expression(e: &Expression) -> String {
    PrettyPrinter::rodin_canonical().print_expression(e)
}

/// Canonicalise an action (assignment).
pub fn canonical_action(a: &Action) -> String {
    PrettyPrinter::rodin_canonical().print_action(a)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::type_env::TypeEnv;
    use rossi::formula::Type;
    use rossi::parse_predicate_str;

    fn canonical_from_str(src: &str) -> String {
        let p = parse_predicate_str(src).unwrap();
        canonical_predicate(&p)
    }

    #[test]
    fn tight_membership() {
        assert_eq!(canonical_from_str("n ∈ ℕ"), "n∈ℕ");
        assert_eq!(canonical_from_str("register ⊆ USERS"), "register⊆USERS");
    }

    #[test]
    fn arithmetic_inside_function_app() {
        // `f(x) ≤ f(y)` → `f(x)≤f(y)`
        let input = parse_predicate_str("f(x) ≤ f(y)").unwrap();
        assert_eq!(canonical_predicate(&input), "f(x)≤f(y)");
    }

    #[test]
    fn logical_chain_is_tight() {
        let p = parse_predicate_str("x ∈ dom(f) ∧ y ∈ dom(f) ∧ x ≤ y").unwrap();
        assert_eq!(canonical_predicate(&p), "x∈dom(f)∧y∈dom(f)∧x≤y");
    }

    /// The typed rendering of an assignment, through the same seam the
    /// checker uses.
    fn canonical_typed_from_str(src: &str, env: &TypeEnv) -> String {
        use rossi::parse_action_str;
        let a = parse_action_str(src).unwrap();
        let typed = crate::sc::typing::typed_assignment(env, &a).expect("assignment type-checks");
        canonical_typed_assignment(&typed)
    }

    #[test]
    fn empty_set_assignment_gets_powerset_ascription() {
        let mut env = TypeEnv::new();
        env.insert("x", Type::pow(Type::Given("USERS".into())));
        assert_eq!(canonical_typed_from_str("x ≔ ∅", &env), "x ≔ ∅ ⦂ ℙ(USERS)");
    }

    #[test]
    fn parallel_assignment_annotates_every_pair() {
        let mut env = TypeEnv::new();
        env.insert("x", Type::pow(Type::Given("USERS".into())));
        env.insert("y", Type::pow(Type::Given("ITEMS".into())));
        assert_eq!(
            canonical_typed_from_str("x, y ≔ ∅, ∅", &env),
            "x,y ≔ ∅ ⦂ ℙ(USERS),∅ ⦂ ℙ(ITEMS)"
        );
    }

    #[test]
    fn integer_assignment_unchanged() {
        let mut env = TypeEnv::new();
        env.insert("n", Type::Int);
        // `0` isn't an empty set — no ascription.
        assert_eq!(canonical_typed_from_str("n ≔ 0", &env), "n ≔ 0");
    }

    #[test]
    fn untyped_assignment_renders_bare() {
        use rossi::parse_action_str;
        // The render-time fallback for a decl with no typed form.
        let a = parse_action_str("x ≔ ∅").unwrap();
        assert_eq!(canonical_action(&a), "x ≔ ∅");
    }

    #[test]
    fn quantified_predicate_matches_rodin() {
        // From binary-search/C0.bcc axm4.
        let p = parse_predicate_str("∀x⦂ℤ, y⦂ℤ · x ∈ dom(f) ∧ y ∈ dom(f) ∧ x ≤ y ⇒ f(x) ≤ f(y)")
            .unwrap();
        assert_eq!(
            canonical_predicate(&p),
            "∀x⦂ℤ,y⦂ℤ·x∈dom(f)∧y∈dom(f)∧x≤y⇒f(x)≤f(y)"
        );
    }

    #[test]
    fn function_override_canonical_form() {
        use rossi::parse_action_str;
        // The parser lowers `f(x) ≔ E` to `f ≔ f\u{E103}{x ↦ E}` directly;
        // the canonical form emits the lowered Assignment.
        let a = parse_action_str("currentFloor(c) ≔ f").unwrap();
        assert_eq!(
            canonical_action(&a),
            "currentFloor ≔ currentFloor\u{E103}{c ↦ f}"
        );
    }

    #[test]
    fn function_override_maplet_arg() {
        use rossi::parse_action_str;
        // Override on a pair domain uses a maplet argument `g(a ↦ b) ≔ y`
        // (function application is single-argument); it lowers to the override
        // `g ≔ g <+ {(a ↦ b) ↦ y}`, the maplet printed flat (left-associative).
        let a = parse_action_str("g(a ↦ b) ≔ y").unwrap();
        assert_eq!(canonical_action(&a), "g ≔ g\u{E103}{a ↦ b ↦ y}");
    }

    /// Rodin keeps relation operators spaced and spells them with private-use
    /// glyphs, while relational override uses a tight private-use glyph.
    #[test]
    fn relation_operators_stay_spaced_with_their_glyph() {
        use rossi::parse_predicate_str;
        let p = parse_predicate_str("r ∈ A <<-> B").unwrap();
        assert_eq!(canonical_predicate(&p), "r∈A \u{E100} B");
    }
}

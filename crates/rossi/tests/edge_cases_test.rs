//! Edge case tests covering AST variants with zero or weak existing coverage.

mod common;

use rossi::ast::expression::{BinaryOp, UnaryOp};
use rossi::ast::predicate::Quantifier;
use rossi::{
    ActionKind, EventStatus, Expression, ExpressionKind, ParseError, Predicate, PredicateKind,
    parse, parse_action_str, parse_expression_str, parse_predicate_str, to_string,
};
use test_case::test_case;

// ============================================================================
// HIGH priority: Action::BecomesIn
// ============================================================================

// Both spellings of becomes-in — Unicode `:∈` and ASCII `::` — must parse to
// the same BecomesIn action.
#[test_case(":∈" ; "unicode")]
#[test_case("::" ; "ascii")]
fn test_becomes_in(op: &str) {
    let source = format!(
        r#"
    MACHINE test
    VARIABLES
        x
    EVENTS
        EVENT INITIALISATION
        THEN
            x := 0
        END

        EVENT choose
        THEN
            x {op} {{1, 2, 3}}
        END
    END
    "#
    );

    let m = common::parse_machine(&source);
    let event = &m.events[0];
    assert_eq!(event.actions.len(), 1);
    match &event.actions[0].action.kind {
        ActionKind::BecomesIn { variables, set } => {
            assert_eq!(variables, &["x"]);
            assert!(
                matches!(set.kind, ExpressionKind::SetEnumeration(_)),
                "Expected SetEnumeration, got {:?}",
                set
            );
        }
        other => panic!("Expected BecomesIn, got {:?}", other),
    }
}

// ============================================================================
// HIGH priority: Action::BecomesSuchThat
// ============================================================================

#[test]
fn test_becomes_such_that() {
    let source = r#"
    MACHINE test
    VARIABLES
        x
    EVENTS
        EVENT INITIALISATION
        THEN
            x := 0
        END

        EVENT pick
        THEN
            x :| x > 0
        END
    END
    "#;

    let m = common::parse_machine(source);
    let event = &m.events[0];
    assert_eq!(event.actions.len(), 1);
    match &event.actions[0].action.kind {
        ActionKind::BecomesSuchThat {
            variables,
            predicate,
        } => {
            assert_eq!(variables, &["x"]);
            assert!(
                matches!(predicate.kind, PredicateKind::Comparison { .. }),
                "Expected Comparison predicate, got {:?}",
                predicate
            );
        }
        other => panic!("Expected BecomesSuchThat, got {:?}", other),
    }
}

// ============================================================================
// HIGH priority: UnaryOp::Inverse
// ============================================================================

// Postfix ∼ (U+223C) is the only spec-defined form; the ASCII ~ (U+007E)
// must parse identically to it.
#[test_case("r = f\u{223C}" ; "unicode")]
#[test_case("r = f~" ; "ascii")]
fn test_inverse_tilde(axiom: &str) {
    let source = common::axiom_context("f, r", axiom);
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Unary { op, operand } => {
            assert_eq!(*op, UnaryOp::Inverse);
            assert!(matches!(&operand.kind, ExpressionKind::Identifier(n) if n == "f"));
        }
        other => panic!("Expected Unary Inverse, got {:?}", other),
    }
}

#[test]
fn test_inverse_repeated() {
    // r∼∼ should parse as (r∼)∼
    let source = common::axiom_context("r, s", "s = r\u{223C}\u{223C}");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Unary {
            op: UnaryOp::Inverse,
            operand,
        } => match &operand.kind {
            ExpressionKind::Unary {
                op: UnaryOp::Inverse,
                operand: inner,
            } => {
                assert!(matches!(&inner.kind, ExpressionKind::Identifier(n) if n == "r"));
            }
            other => panic!("Expected nested Inverse, got {:?}", other),
        },
        other => panic!("Expected Unary Inverse, got {:?}", other),
    }
}

#[test]
fn test_inverse_relational_image() {
    // r∼[S] should parse as (r∼)[S]
    let source = common::axiom_context("r, S, T", "T = r\u{223C}[S]");
    let rhs = common::parse_axiom_rhs(&source);
    assert!(
        matches!(&rhs.kind, ExpressionKind::RelationalImage { relation, .. }
            if matches!(&relation.kind, ExpressionKind::Unary { op: UnaryOp::Inverse, .. })),
        "Expected RelationalImage with Inverse relation, got {:?}",
        rhs
    );
}

#[test]
fn test_inverse_function_application() {
    // f∼(x) should parse as (f∼)(x)
    let source = common::axiom_context("f, x, y", "y = f\u{223C}(x)");
    let rhs = common::parse_axiom_rhs(&source);
    assert!(
        matches!(&rhs.kind, ExpressionKind::FunctionApplication { function, .. }
            if matches!(&function.kind, ExpressionKind::Unary { op: UnaryOp::Inverse, .. })),
        "Expected FunctionApplication with Inverse function, got {:?}",
        rhs
    );
}

// ============================================================================
// HIGH priority: BinaryOp::Semicolon (forward composition)
// ============================================================================

#[test]
fn test_forward_composition() {
    // In expression context (not action), semicolon is forward composition
    let source = common::axiom_context("f, g, r", "r = f ; g");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary { op, left, right } => {
            assert_eq!(*op, BinaryOp::Semicolon);
            assert!(matches!(&left.kind, ExpressionKind::Identifier(n) if n == "f"));
            assert!(matches!(&right.kind, ExpressionKind::Identifier(n) if n == "g"));
        }
        other => panic!("Expected Binary Semicolon, got {:?}", other),
    }
}

#[test]
fn test_forward_composition_parenthesized_in_action() {
    // In an action RHS, forward composition must be parenthesized
    let source = r#"
    MACHINE test
    VARIABLES
        x
    EVENTS
        EVENT INITIALISATION
        THEN
            x := 0
        END

        EVENT apply
        THEN
            x := (f ; g)
        END
    END
    "#;

    let m = common::parse_machine(source);
    let event = &m.events[0];
    assert_eq!(event.actions.len(), 1);
    match &event.actions[0].action.kind {
        ActionKind::Assignment { assignments } => {
            assert_eq!(assignments.len(), 1);
            assert_eq!(assignments[0].0, "x");
            // The parenthesized (f ; g) should parse as forward composition
            assert!(
                matches!(
                    &assignments[0].1.kind,
                    ExpressionKind::Binary {
                        op: BinaryOp::Semicolon,
                        ..
                    }
                ),
                "Expected Semicolon composition in parens, got {:?}",
                assignments[0].1
            );
        }
        other => panic!("Expected Assignment, got {:?}", other),
    }
}

#[test]
fn test_standalone_action_forward_composition_unparenthesized() {
    // A standalone action string (one action, as in a Rodin XML assignment
    // attribute) has no following action to separate, so a bare semicolon
    // is forward composition.
    let action = rossi::parse_action_str("x ≔ f;g").expect("standalone action parses");
    let ActionKind::Assignment { assignments } = &action.kind else {
        panic!("Expected Assignment, got {:?}", action);
    };
    assert_eq!(assignments.len(), 1);
    assert_eq!(assignments[0].0, "x");
    let ExpressionKind::Binary { op, left, right } = &assignments[0].1.kind else {
        panic!("Expected Binary, got {:?}", assignments[0].1);
    };
    assert_eq!(*op, BinaryOp::Semicolon);
    assert!(matches!(&left.kind, ExpressionKind::Identifier(n) if n == "f"));
    assert!(matches!(&right.kind, ExpressionKind::Identifier(n) if n == "g"));
}

#[test]
fn test_standalone_action_chained_composition_with_inverse() {
    // Left-associative chain mixing inverse and a parenthesized set
    // expression: h∼;(s ∪ t);h parses as (h∼;(s ∪ t));h.
    let action = rossi::parse_action_str("x ≔ h∼;(s ∪ t);h").expect("standalone action parses");
    let ActionKind::Assignment { assignments } = &action.kind else {
        panic!("Expected Assignment, got {:?}", action);
    };
    let ExpressionKind::Binary { op, left, right } = &assignments[0].1.kind else {
        panic!("Expected Binary, got {:?}", assignments[0].1);
    };
    assert_eq!(*op, BinaryOp::Semicolon);
    assert!(matches!(&right.kind, ExpressionKind::Identifier(n) if n == "h"));
    let ExpressionKind::Binary { op, left, .. } = &left.kind else {
        panic!("Expected nested Binary, got {:?}", left);
    };
    assert_eq!(*op, BinaryOp::Semicolon);
    assert!(matches!(
        &left.kind,
        ExpressionKind::Unary {
            op: UnaryOp::Inverse,
            ..
        }
    ));
}

#[test]
fn test_standalone_becomes_such_that_with_composition() {
    let action = rossi::parse_action_str("x :∣ x' = f;g").expect("standalone action parses");
    let ActionKind::BecomesSuchThat { predicate, .. } = &action.kind else {
        panic!("Expected BecomesSuchThat, got {:?}", action);
    };
    let PredicateKind::Comparison { right, .. } = &predicate.kind else {
        panic!("Expected Comparison, got {:?}", predicate);
    };
    assert!(matches!(
        right.kind,
        ExpressionKind::Binary {
            op: BinaryOp::Semicolon,
            ..
        }
    ));
}

// ============================================================================
// HIGH priority: EventStatus::Anticipated
// ============================================================================

#[test]
fn test_anticipated_event() {
    let source = r#"
    MACHINE test
    VARIABLES
        x
    VARIANT
        x
    EVENTS
        EVENT INITIALISATION
        THEN
            x := 10
        END

        EVENT step
        STATUS anticipated
        WHERE
            @grd1 x > 0
        THEN
            x := x - 1
        END
    END
    "#;

    let m = common::parse_machine(source);
    assert_eq!(m.events.len(), 1);
    assert_eq!(m.events[0].status, Some(EventStatus::Anticipated));
}

// ============================================================================
// MEDIUM priority: BinaryOp::Composition via circ
// ============================================================================

#[test]
fn test_composition_circ_ascii() {
    let source = common::axiom_context("f, g, r", "r = f circ g");
    let rhs = common::parse_axiom_rhs(&source);
    assert!(
        matches!(
            &rhs.kind,
            ExpressionKind::Binary {
                op: BinaryOp::Composition,
                ..
            }
        ),
        "Expected Composition via 'circ', got {:?}",
        rhs
    );
}

// ============================================================================
// MEDIUM priority: Quantifiers with multiple variables
// ============================================================================

#[test_case("∀x, y · x > 0 ∧ y > 0 ⇒ x + y > 0", Quantifier::ForAll ; "forall")]
#[test_case("∃x, y · x > 0 ∧ y > 0", Quantifier::Exists ; "exists")]
fn test_quantifier_multiple_variables(axiom: &str, expected: Quantifier) {
    let source = format!("\n    CONTEXT test\n    AXIOMS\n        @axm1 {axiom}\n    END\n    ");

    let ctx = common::parse_context(&source);
    match &ctx.axioms[0].predicate.kind {
        PredicateKind::Quantified {
            quantifier,
            identifiers,
            predicate,
        } => {
            assert_eq!(*quantifier, expected);
            assert_eq!(identifiers, &["x", "y"]);
            assert!(
                matches!(&predicate.kind, PredicateKind::Logical { .. }),
                "Expected Logical predicate body, got {:?}",
                predicate
            );
        }
        other => panic!("Expected Quantified {expected:?}, got {:?}", other),
    }
}

#[test]
fn test_nested_quantifiers() {
    let source = r#"
    CONTEXT test
    AXIOMS
        @axm1 ∀x · (∃y · x + y = 0)
    END
    "#;

    let ctx = common::parse_context(source);
    match &ctx.axioms[0].predicate.kind {
        PredicateKind::Quantified {
            quantifier,
            identifiers,
            predicate,
        } => {
            assert_eq!(*quantifier, Quantifier::ForAll);
            assert_eq!(identifiers, &["x"]);
            assert!(
                matches!(
                    &predicate.kind,
                    PredicateKind::Quantified {
                        quantifier: Quantifier::Exists,
                        ..
                    }
                ),
                "Expected Quantified Exists inside ForAll, got {:?}",
                predicate
            );
        }
        other => panic!("Expected Quantified ForAll, got {:?}", other),
    }
}

// ============================================================================
// MEDIUM priority: Lambda with ident-pattern
// ============================================================================

#[test]
fn test_lambda_maplet_pattern() {
    use rossi::IdentPattern;

    let source = r#"
    CONTEXT test
    CONSTANTS
        f
    AXIOMS
        @axm1 f = λx ↦ y · x ∈ ℕ ∧ y ∈ ℕ ∣ x + y
    END
    "#;

    let ctx = common::parse_context(source);
    if let PredicateKind::Comparison { right, .. } = &ctx.axioms[0].predicate.kind {
        match &right.kind {
            ExpressionKind::Lambda {
                pattern,
                predicate,
                expression,
            } => {
                let ids = pattern.identifiers();
                assert_eq!(ids, vec!["x", "y"]);
                assert!(matches!(
                    pattern,
                    IdentPattern::Maplet(l, r)
                        if matches!(l.as_ref(), IdentPattern::Identifier(n) if n == "x")
                        && matches!(r.as_ref(), IdentPattern::Identifier(n) if n == "y")
                ));
                assert!(matches!(&predicate.kind, PredicateKind::Logical { .. }));
                assert!(matches!(&expression.kind, ExpressionKind::Binary { .. }));
            }
            other => panic!("Expected Lambda, got {:?}", other),
        }
    } else {
        panic!("Expected Comparison predicate");
    }
}

#[test]
fn test_lambda_parenthesized_maplet_pattern() {
    use rossi::IdentPattern;

    // This is a real-world corpus pattern that originally failed
    let source = r#"
    CONTEXT test
    CONSTANTS
        DIST
    AXIOMS
        @axm1 DIST = λ(x↦y) · x ∈ ℤ ∧ y ∈ ℤ ∣ max({y − x, x − y})
    END
    "#;

    let ctx = common::parse_context(source);
    if let PredicateKind::Comparison { right, .. } = &ctx.axioms[0].predicate.kind {
        match &right.kind {
            ExpressionKind::Lambda { pattern, .. } => {
                let ids = pattern.identifiers();
                assert_eq!(ids, vec!["x", "y"]);
                assert!(matches!(
                    pattern,
                    IdentPattern::Maplet(l, r)
                        if matches!(l.as_ref(), IdentPattern::Identifier(n) if n == "x")
                        && matches!(r.as_ref(), IdentPattern::Identifier(n) if n == "y")
                ));
            }
            other => panic!("Expected Lambda, got {:?}", other),
        }
    } else {
        panic!("Expected Comparison predicate");
    }
}

#[test]
fn test_lambda_triple_maplet_left_assoc() {
    use rossi::IdentPattern;

    let source = r#"
    CONTEXT test
    CONSTANTS
        f
    AXIOMS
        @axm1 f = λx ↦ y ↦ z · x ∈ ℤ ∣ x
    END
    "#;

    let ctx = common::parse_context(source);
    if let PredicateKind::Comparison { right, .. } = &ctx.axioms[0].predicate.kind {
        match &right.kind {
            ExpressionKind::Lambda { pattern, .. } => {
                let ids = pattern.identifiers();
                assert_eq!(ids, vec!["x", "y", "z"]);
                // Left-assoc: (x ↦ y) ↦ z
                match pattern {
                    IdentPattern::Maplet(left, right) => {
                        assert!(matches!(right.as_ref(), IdentPattern::Identifier(n) if n == "z"));
                        match left.as_ref() {
                            IdentPattern::Maplet(ll, lr) => {
                                assert!(
                                    matches!(ll.as_ref(), IdentPattern::Identifier(n) if n == "x")
                                );
                                assert!(
                                    matches!(lr.as_ref(), IdentPattern::Identifier(n) if n == "y")
                                );
                            }
                            other => panic!("Expected inner Maplet, got {:?}", other),
                        }
                    }
                    other => panic!("Expected outer Maplet, got {:?}", other),
                }
            }
            other => panic!("Expected Lambda, got {:?}", other),
        }
    } else {
        panic!("Expected Comparison predicate");
    }
}

// ============================================================================
// MEDIUM priority: Set comprehension with multiple variables
// ============================================================================

#[test]
fn test_set_comprehension_multiple_vars() {
    let source = common::invariant_machine("s", "s = {x, y · x ∈ ℕ ∧ y ∈ ℕ | x + y}");
    let m = common::parse_machine(&source);
    if let PredicateKind::Comparison { right, .. } = &m.invariants[0].predicate.kind {
        match &right.kind {
            ExpressionKind::SetComprehension {
                identifiers,
                predicate,
                expression,
            } => {
                assert_eq!(identifiers.len(), 2);
                assert_eq!(identifiers[0], "x");
                assert_eq!(identifiers[1], "y");
                assert!(matches!(&predicate.kind, PredicateKind::Logical { .. }));
                assert!(expression.is_some());
            }
            other => panic!("Expected SetComprehension, got {:?}", other),
        }
    } else {
        panic!("Expected Comparison predicate");
    }
}

// ============================================================================
// Primed identifiers (after-state variables like x')
// ============================================================================

#[test]
fn test_primed_identifier_in_becomes_such_that() {
    let source = std::fs::read_to_string("examples/refinement_abstract.eventb")
        .expect("Failed to read refinement_abstract.eventb");

    let m = common::parse_machine(&source);
    // Find the "decrease" event
    let decrease = m
        .events
        .iter()
        .find(|e| e.name == "decrease")
        .expect("Expected 'decrease' event");
    assert_eq!(decrease.actions.len(), 1);
    match &decrease.actions[0].action.kind {
        ActionKind::BecomesSuchThat {
            variables,
            predicate,
        } => {
            assert_eq!(variables, &["abstract_state"]);
            // The predicate should contain abstract_state' as an identifier
            fn contains_primed_ident(pred: &Predicate) -> bool {
                match &pred.kind {
                    PredicateKind::Comparison { left, right, .. } => {
                        has_primed_expr(left) || has_primed_expr(right)
                    }
                    PredicateKind::Logical { left, right, .. } => {
                        contains_primed_ident(left) || contains_primed_ident(right)
                    }
                    _ => false,
                }
            }
            fn has_primed_expr(expr: &Expression) -> bool {
                match &expr.kind {
                    ExpressionKind::Identifier(name) => name.ends_with('\''),
                    ExpressionKind::Binary { left, right, .. } => {
                        has_primed_expr(left) || has_primed_expr(right)
                    }
                    _ => false,
                }
            }
            assert!(
                contains_primed_ident(predicate),
                "Expected predicate to contain primed identifier (abstract_state'), got {:?}",
                predicate
            );
        }
        other => panic!("Expected BecomesSuchThat, got {:?}", other),
    }
}

// ============================================================================
// Regression: a `VARIANT` whose expression starts with `(`, sitting right
// after an `INVARIANTS`/`THEOREMS` section, must parse and round-trip.
//
// Before the fix, the section's `(labeled_predicate)*` repetition was
// unguarded: it speculatively parsed the following `VARIANT` keyword as a
// permissive `identifier`, absorbed the `(…)` as a function-application
// argument, and only failed at `EVENTS`. The follow-set guard
// (`!machine_section_kw` / `!context_section_kw`) stops the list at the
// section boundary — the textual counterpart of how Camille/ProB/CamilleX
// bound a formula against structural keywords.
//
// Originally surfaced by the import→re-parse round-trip on corpus models
// whose machines declare such a variant (see rossi-build `import_corpus`).
// ============================================================================

/// `parse` succeeds and `print → re-parse → re-print` is byte-stable — the
/// same property `import_corpus` checks against the corpus.
fn assert_stable_roundtrip(source: &str) {
    let component = parse(source).expect("parse should succeed");
    let printed = to_string(&component);
    let reparsed = parse(&printed).expect("printed form must re-parse");
    assert_eq!(
        printed,
        to_string(&reparsed),
        "round-trip must be byte-stable"
    );
}

#[test]
fn variant_paren_expr_after_invariants_roundtrips() {
    assert_stable_roundtrip(
        r#"MACHINE m
VARIABLES
    a
    b
    c
INVARIANTS
    @inv1 a ∈ ℙ(b)
VARIANT
    (a × b) ∖ c
EVENTS
    EVENT INITIALISATION
    THEN
        @act1 a ≔ a
    END
END
"#,
    );
}

#[test]
fn variant_paren_expr_after_theorems_roundtrips() {
    assert_stable_roundtrip(
        r#"MACHINE m
VARIABLES
    a
    b
    c
THEOREMS
    @thm1 a ∈ ℙ(b)
VARIANT
    (a × b) ∖ c
EVENTS
    EVENT INITIALISATION
    THEN
        @act1 a ≔ a
    END
END
"#,
    );
}

#[test]
fn context_theorems_paren_predicate_after_axioms_parses() {
    // Symmetric context case: a `THEOREMS` section whose first predicate is a
    // bare parenthesized predicate, following an `AXIOMS` section. Before the
    // `!context_section_kw` guard, the AXIOMS `(labeled_predicate)*` swallowed
    // the `THEOREMS` keyword + `(…)` and failed at `END`.
    //
    // Asserts parse only (not byte-stable round-trip): printing an *unlabeled*
    // theorem is a separate, orthogonal limitation and is not what this guard
    // addresses.
    let source = r#"CONTEXT c
SETS
    S
CONSTANTS
    x
AXIOMS
    @axm1 x ∈ S
THEOREMS
    (x ∈ S)
END
"#;
    parse(source).expect("AXIOMS list must not swallow the following THEOREMS section");
}

// ============================================================================
// Structural separators (whitespace, not comma) — EXTENDS, SETS, CONSTANTS,
// SEES, VARIABLES, event ANY.
//
// Declared identifiers and component references are separated by whitespace,
// never by a comma — that mirrors how the real Event-B text tools work, and
// how Rodin stores each as its own model element. A comma is meaningful only
// inside formulas (set extension, quantifier lists, `partition`, parallel
// assignment, function-update sets), where it stays a separator.
// ============================================================================

/// Every clause spelled with a comma between items must fail to parse.
const COMMA_FORMS: &[&str] = &[
    "CONTEXT c EXTENDS a, b END",
    "CONTEXT c SETS S, T END",
    "CONTEXT c CONSTANTS a, b END",
    "MACHINE m SEES c1, c2 END",
    "MACHINE m VARIABLES x, y END",
    "MACHINE m EVENTS EVENT e ANY a, b END END",
];

/// The same clauses with whitespace separation must parse. "Whitespace" is
/// any run of space / tab / CR / newline, so the common
/// one-identifier-per-line block and tab separation parse identically.
const WHITESPACE_FORMS: &[&str] = &[
    "CONTEXT c EXTENDS a b END",
    "CONTEXT c SETS S T END",
    "CONTEXT c CONSTANTS a b END",
    "MACHINE m SEES c1 c2 END",
    "MACHINE m VARIABLES x y END",
    "MACHINE m EVENTS EVENT e ANY a b END END",
    // Newline / tab separated multi-line forms.
    "CONTEXT c\nSETS\n    S\n    T\nEND",
    "CONTEXT c\nCONSTANTS\n\ta\n\tb\nEND",
    "MACHINE m\nVARIABLES\n    x\n    y\nEND",
    "MACHINE m\nEVENTS\n    EVENT e\n    ANY\n        a\n        b\n    END\nEND",
];

#[test]
fn comma_rejected_in_every_structural_clause() {
    for src in COMMA_FORMS {
        assert!(
            parse(src).is_err(),
            "a comma must not separate structural list items: {src}"
        );
    }
}

#[test]
fn whitespace_accepted_in_every_structural_clause() {
    for src in WHITESPACE_FORMS {
        parse(src).unwrap_or_else(|e| panic!("whitespace form must parse: {e:?}\n{src}"));
    }
}

#[test]
fn commas_still_parse_inside_formulas() {
    // Set extension, quantifier ident-list, partition, function-update set.
    for src in ["{a, b, c}", "f{x ↦ y, u ↦ v}"] {
        parse_expression_str(src)
            .unwrap_or_else(|e| panic!("formula comma must parse: {e:?}\n{src}"));
    }
    for src in ["∀x, y · x = y", "partition(S, a, b)"] {
        parse_predicate_str(src)
            .unwrap_or_else(|e| panic!("formula comma must parse: {e:?}\n{src}"));
    }
    // Parallel assignment: comma separates both targets and values.
    parse_action_str("x, y := 1, 2")
        .unwrap_or_else(|e| panic!("parallel assignment must parse: {e:?}"));
}

#[test]
fn parallel_assignment_requires_matching_target_and_expression_counts() {
    for (src, targets, expressions, operator) in [
        ("x, y := 1", 2, 1, ":="),
        ("x := 1, 2", 1, 2, ":="),
        ("x, y ≔ 1", 2, 1, "≔"),
        ("x ≔ 1, 2", 1, 2, "≔"),
    ] {
        let error = parse_action_str(src)
            .expect_err("mismatched parallel assignment must not produce an action");
        let (actual_targets, actual_expressions, line, column, span) = match error {
            ParseError::AssignmentArityMismatch {
                targets,
                expressions,
                line,
                column,
                span: Some(span),
            } => (targets, expressions, line, column, span),
            other => panic!("expected assignment arity error for {src:?}, got {other:?}"),
        };
        assert_eq!((actual_targets, actual_expressions), (targets, expressions));
        assert_eq!(line, 1);
        assert_eq!(column, src[..span.start].chars().count() + 1);
        assert_eq!(&src[span.start..span.end], operator);
    }
}

#[test]
fn any_parameters_round_trip_without_commas() {
    let machine = parse("MACHINE m EVENTS EVENT e ANY p q r END END").unwrap();
    let printed = to_string(&machine);
    assert!(
        printed.contains("p q r") && !printed.contains("p, q"),
        "ANY parameters must print whitespace-separated:\n{printed}"
    );
    parse(&printed).unwrap_or_else(|e| panic!("pretty output must reparse: {e:?}\n{printed}"));
}

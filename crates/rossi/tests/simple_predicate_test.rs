//! Test for debugging predicate parsing

mod common;

use rossi::ast::predicate::LogicalOp;
use rossi::{ActionKind, ExpressionKind, parse, parse_action_str, parse_expression_str};

#[test]
fn test_binary_addition_ast_structure() {
    use rossi::ast::expression::BinaryOp;
    use rossi::ast::predicate::ComparisonOp;
    use rossi::{ExpressionKind, PredicateKind};

    let source = r#"
    CONTEXT test
    CONSTANTS
        a b c
    AXIOMS
        @axm1 c = a + b
    END
    "#;

    let ctx = common::parse_context(source);
    assert_eq!(ctx.axioms.len(), 1);
    let pred = &ctx.axioms[0].predicate;

    // The predicate should be: c = (a + b)
    match &pred.kind {
        PredicateKind::Comparison { op, left, right } => {
            assert_eq!(*op, ComparisonOp::Equal);
            assert!(matches!(&left.kind, ExpressionKind::Identifier(name) if name == "c"));
            // right should be Binary { op: Add, left: a, right: b }
            match &right.kind {
                ExpressionKind::Binary {
                    op: bin_op,
                    left: bin_left,
                    right: bin_right,
                } => {
                    assert_eq!(*bin_op, BinaryOp::Add);
                    assert!(
                        matches!(&bin_left.kind, ExpressionKind::Identifier(name) if name == "a")
                    );
                    assert!(
                        matches!(&bin_right.kind, ExpressionKind::Identifier(name) if name == "b")
                    );
                }
                other => panic!("Expected Binary expression, got {:?}", other),
            }
        }
        other => panic!("Expected Comparison predicate, got {:?}", other),
    }
}

#[test]
fn test_chained_binary_operations() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    let source = r#"
    CONTEXT test
    CONSTANTS
        a b c d
    AXIOMS
        @axm1 d = a + b + c
    END
    "#;

    let ctx = common::parse_context(source);
    if let rossi::PredicateKind::Comparison { right, .. } = &ctx.axioms[0].predicate.kind {
        // a + b + c should be ((a + b) + c) - left associative
        match &right.kind {
            ExpressionKind::Binary {
                op,
                left,
                right: right_c,
            } => {
                assert_eq!(*op, BinaryOp::Add);
                assert!(matches!(&right_c.kind, ExpressionKind::Identifier(name) if name == "c"));
                // left should be (a + b)
                match &left.kind {
                    ExpressionKind::Binary {
                        op: inner_op,
                        left: inner_left,
                        right: inner_right,
                    } => {
                        assert_eq!(*inner_op, BinaryOp::Add);
                        assert!(
                            matches!(&inner_left.kind, ExpressionKind::Identifier(name) if name == "a")
                        );
                        assert!(
                            matches!(&inner_right.kind, ExpressionKind::Identifier(name) if name == "b")
                        );
                    }
                    other => panic!("Expected inner Binary, got {:?}", other),
                }
            }
            other => panic!("Expected Binary expression, got {:?}", other),
        }
    }
}

// All spellings of the binary logical operators: Unicode ∧ plus the ASCII
// forms & (AND) and `or` (OR).
#[test_case::test_case("x > 0 ∧ y > 0", LogicalOp::And ; "conjunction_unicode")]
#[test_case::test_case("x > 0 & y > 0", LogicalOp::And ; "conjunction_ascii_ampersand")]
#[test_case::test_case("x > 0 or y > 0", LogicalOp::Or ; "disjunction_ascii_or")]
fn test_logical_operator_spellings(invariant_body: &str, expected: LogicalOp) {
    use rossi::PredicateKind;

    let source = common::invariant_machine("x y", invariant_body);
    let m = common::parse_machine(&source);
    let pred = &m.invariants[0].predicate;
    match &pred.kind {
        PredicateKind::Logical { op, left, right } => {
            assert_eq!(*op, expected);
            assert!(matches!(&left.kind, PredicateKind::Comparison { .. }));
            assert!(matches!(&right.kind, PredicateKind::Comparison { .. }));
        }
        other => panic!("Expected Logical predicate, got {:?}", other),
    }
}

#[test]
fn test_chained_binary_predicates() {
    use rossi::PredicateKind;
    use rossi::ast::predicate::LogicalOp;

    let m = common::parse_machine(
        r#"
    MACHINE test
    VARIABLES
        x y z
    INVARIANTS
        @inv1 x > 0 ∧ y > 0 ∧ z > 0
    END
    "#,
    );
    let pred = &m.invariants[0].predicate;

    // Should be ((x > 0) ∧ (y > 0)) ∧ (z > 0) - left associative
    match &pred.kind {
        PredicateKind::Logical { op, left, right } => {
            assert_eq!(*op, LogicalOp::And);
            assert!(matches!(&right.kind, PredicateKind::Comparison { .. }));
            match &left.kind {
                PredicateKind::Logical {
                    op: inner_op,
                    left: inner_left,
                    right: inner_right,
                } => {
                    assert_eq!(*inner_op, LogicalOp::And);
                    assert!(matches!(&inner_left.kind, PredicateKind::Comparison { .. }));
                    assert!(matches!(
                        &inner_right.kind,
                        PredicateKind::Comparison { .. }
                    ));
                }
                other => panic!("Expected inner Logical, got {:?}", other),
            }
        }
        other => panic!("Expected Logical predicate, got {:?}", other),
    }
}

#[test]
fn test_lambda_expression() {
    use rossi::{ExpressionKind, IdentPattern};

    let source = r#"
    CONTEXT test
    CONSTANTS
        f
    AXIOMS
        @axm1 f = λx·x ∈ ℕ ∣ x + 1
    END
    "#;

    let result = parse(source);
    if let Err(e) = &result {
        eprintln!("Parse error: {:?}", e);
    }
    assert!(result.is_ok(), "Lambda expression should parse correctly");

    let ctx = common::parse_context(source);
    if let rossi::PredicateKind::Comparison { right, .. } = &ctx.axioms[0].predicate.kind {
        match &right.kind {
            ExpressionKind::Lambda {
                pattern,
                predicate,
                expression,
            } => {
                assert!(matches!(pattern, IdentPattern::Identifier(name) if name == "x"));
                assert!(matches!(
                    predicate.kind,
                    rossi::PredicateKind::Comparison { .. }
                ));
                assert!(matches!(expression.kind, ExpressionKind::Binary { .. }));
            }
            other => panic!("Expected Lambda expression, got {:?}", other),
        }
    }
}

// ============================================================================
// Unary expression parsing tests
// ============================================================================

macro_rules! test_unary_op {
    ($name:ident, $constants:expr, $axiom:expr, $expected:expr) => {
        #[test]
        fn $name() {
            use rossi::ast::expression::UnaryOp;
            use rossi::ExpressionKind;

            let source = common::axiom_context($constants, $axiom);
            let rhs = common::parse_axiom_rhs(&source);
            assert!(
                matches!(&rhs.kind, ExpressionKind::Unary { op, .. } if *op == $expected),
                "Expected {:?}, got {:?}",
                $expected,
                rhs
            );
        }
    };
}

test_unary_op!(test_unary_domain, "f, d", "d = dom(f)", UnaryOp::Domain);
test_unary_op!(test_unary_range, "f, r", "r = ran(f)", UnaryOp::Range);
test_unary_op!(test_unary_powerset, "S, P", "P = POW(S)", UnaryOp::PowerSet);
test_unary_op!(
    test_unary_powerset1,
    "S, P",
    "P = POW1(S)",
    UnaryOp::PowerSet1
);
test_unary_op!(test_unary_minus, "x, y", "y = -x", UnaryOp::Minus);

#[test]
fn test_nested_unary() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::UnaryOp;

    let source = common::axiom_context("f, r", "r = dom(ran(f))");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Unary { op, operand } => {
            assert_eq!(*op, UnaryOp::Domain);
            match &operand.kind {
                ExpressionKind::Unary {
                    op: inner_op,
                    operand: inner_operand,
                } => {
                    assert_eq!(*inner_op, UnaryOp::Range);
                    assert!(matches!(
                        &inner_operand.kind,
                        ExpressionKind::Identifier(name) if name == "f"
                    ));
                }
                other => panic!("Expected inner Unary, got {:?}", other),
            }
        }
        other => panic!("Expected Unary expression, got {:?}", other),
    }
}

#[test]
fn test_unary_in_binary() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::{BinaryOp, UnaryOp};

    let source = common::axiom_context("f, g, result", "result = dom(f) \u{222A} ran(g)");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary { op, left, right } => {
            assert_eq!(*op, BinaryOp::Union);
            assert!(matches!(
                &left.kind,
                ExpressionKind::Unary {
                    op: UnaryOp::Domain,
                    ..
                }
            ));
            assert!(matches!(
                &right.kind,
                ExpressionKind::Unary {
                    op: UnaryOp::Range,
                    ..
                }
            ));
        }
        other => panic!("Expected Binary expression, got {:?}", other),
    }
}

// ============================================================================
// Negation predicate parsing tests
// ============================================================================

#[test_case::test_case("¬(x > 0)" ; "unicode")]
#[test_case::test_case("not(x > 0)" ; "ascii")]
fn test_negation(invariant_body: &str) {
    use rossi::PredicateKind;

    let source = common::invariant_machine("x", invariant_body);
    let m = common::parse_machine(&source);
    let pred = &m.invariants[0].predicate;
    match &pred.kind {
        PredicateKind::Not(inner) => {
            assert!(matches!(&inner.kind, PredicateKind::Comparison { .. }));
        }
        other => panic!("Expected Not predicate, got {:?}", other),
    }
}

#[test]
fn test_double_negation() {
    use rossi::PredicateKind;

    let m = common::parse_machine(
        r#"
    MACHINE test
    VARIABLES
        x
    INVARIANTS
        @inv1 ¬(¬(x > 0))
    END
    "#,
    );
    let pred = &m.invariants[0].predicate;
    match &pred.kind {
        PredicateKind::Not(inner) => match &inner.kind {
            PredicateKind::Not(inner2) => {
                assert!(matches!(&inner2.kind, PredicateKind::Comparison { .. }));
            }
            other => panic!("Expected inner Not, got {:?}", other),
        },
        other => panic!("Expected Not predicate, got {:?}", other),
    }
}

// ============================================================================
// Binary operator tests
// ============================================================================

macro_rules! test_binary_op {
    ($name:ident, $constants:expr, $axiom:expr, $expected:expr) => {
        #[test]
        fn $name() {
            use rossi::ast::expression::BinaryOp;
            use rossi::ExpressionKind;

            let source = common::axiom_context($constants, $axiom);
            let rhs = common::parse_axiom_rhs(&source);
            assert!(
                matches!(&rhs.kind, ExpressionKind::Binary { op, .. } if *op == $expected),
                "Expected {:?}, got {:?}",
                $expected,
                rhs
            );
        }
    };
}

#[test]
fn test_maplet_ascii() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    let source = common::axiom_context("x, y, r", "r = x |-> y");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary { op, left, right } => {
            assert_eq!(*op, BinaryOp::Maplet);
            assert!(matches!(&left.kind, ExpressionKind::Identifier(n) if n == "x"));
            assert!(matches!(&right.kind, ExpressionKind::Identifier(n) if n == "y"));
        }
        other => panic!("Expected Maplet, got {:?}", other),
    }
}

test_binary_op!(
    test_maplet_unicode,
    "x, y, r",
    "r = x \u{21A6} y",
    BinaryOp::Maplet
);

#[test]
fn test_maplet_left_associative() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    let source = common::axiom_context("a, b, c, r", "r = a |-> b |-> c");
    let rhs = common::parse_axiom_rhs(&source);
    // Left-associative per spec p.18: a |-> b |-> c = (a |-> b) |-> c
    match &rhs.kind {
        ExpressionKind::Binary { op, left, right } => {
            assert_eq!(*op, BinaryOp::Maplet);
            assert!(matches!(&right.kind, ExpressionKind::Identifier(n) if n == "c"));
            match &left.kind {
                ExpressionKind::Binary {
                    op: inner_op,
                    left: inner_left,
                    right: inner_right,
                } => {
                    assert_eq!(*inner_op, BinaryOp::Maplet);
                    assert!(matches!(&inner_left.kind, ExpressionKind::Identifier(n) if n == "a"));
                    assert!(matches!(&inner_right.kind, ExpressionKind::Identifier(n) if n == "b"));
                }
                other => panic!("Expected inner Maplet, got {:?}", other),
            }
        }
        other => panic!("Expected Maplet, got {:?}", other),
    }
}

#[test]
fn test_maplet_binds_looser_than_relation_arrow() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    // kernel_lang Table 3.1: pair constructor binds looser than relation
    // arrows, so a ↦ b ↔ c = a ↦ (b ↔ c).
    let source = common::axiom_context("a, b, c, r", "r = a \u{21A6} b \u{2194} c");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary { op, left, right } => {
            assert_eq!(*op, BinaryOp::Maplet);
            assert!(matches!(&left.kind, ExpressionKind::Identifier(n) if n == "a"));
            match &right.kind {
                ExpressionKind::Binary {
                    op: inner_op,
                    left: inner_left,
                    right: inner_right,
                } => {
                    assert_eq!(*inner_op, BinaryOp::Relation);
                    assert!(matches!(&inner_left.kind, ExpressionKind::Identifier(n) if n == "b"));
                    assert!(matches!(&inner_right.kind, ExpressionKind::Identifier(n) if n == "c"));
                }
                other => panic!("Expected inner Relation, got {:?}", other),
            }
        }
        other => panic!("Expected Maplet, got {:?}", other),
    }
}

#[test]
fn test_maplet_binds_looser_than_total_fn_arrow() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    // a ↦ b → c = a ↦ (b → c)
    let source = common::axiom_context("a, b, c, r", "r = a \u{21A6} b \u{2192} c");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary { op, right, .. } => {
            assert_eq!(*op, BinaryOp::Maplet);
            assert!(matches!(
                &right.kind,
                ExpressionKind::Binary {
                    op: BinaryOp::TotalFunction,
                    ..
                }
            ));
        }
        other => panic!("Expected Maplet, got {:?}", other),
    }
}

#[test]
fn test_maplet_binds_looser_than_relation_arrow_ascii() {
    // ASCII spellings parse to the same AST as the Unicode form.
    let unicode = common::parse_axiom_rhs(&common::axiom_context(
        "a, b, c, r",
        "r = a \u{21A6} b \u{2194} c",
    ));
    let ascii = common::parse_axiom_rhs(&common::axiom_context("a, b, c, r", "r = a |-> b <-> c"));
    assert_eq!(unicode, ascii);
}

#[test]
fn test_parenthesized_maplet_keeps_grouping_under_arrow() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    // Explicit parens override precedence: (a ↦ b) ↔ c stays a Relation.
    let source = common::axiom_context("a, b, c, r", "r = (a \u{21A6} b) \u{2194} c");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary { op, left, right } => {
            assert_eq!(*op, BinaryOp::Relation);
            assert!(matches!(
                &left.kind,
                ExpressionKind::Binary {
                    op: BinaryOp::Maplet,
                    ..
                }
            ));
            assert!(matches!(&right.kind, ExpressionKind::Identifier(n) if n == "c"));
        }
        other => panic!("Expected Relation, got {:?}", other),
    }
}

#[test]
fn test_maplet_chain_with_arrow_operands() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    // Pair-expression operands may each contain one (non-associative) arrow:
    // a ↔ b ↦ c ↔ d = (a ↔ b) ↦ (c ↔ d). Rejected by the old
    // (inverted-precedence) grammar, which allowed only one arrow per chain.
    let source = common::axiom_context("a, b, c, d, r", "r = a \u{2194} b \u{21A6} c \u{2194} d");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary { op, left, right } => {
            assert_eq!(*op, BinaryOp::Maplet);
            assert!(matches!(
                &left.kind,
                ExpressionKind::Binary {
                    op: BinaryOp::Relation,
                    ..
                }
            ));
            assert!(matches!(
                &right.kind,
                ExpressionKind::Binary {
                    op: BinaryOp::Relation,
                    ..
                }
            ));
        }
        other => panic!("Expected Maplet, got {:?}", other),
    }
}

#[test]
fn test_maplet_binds_looser_than_arrow_in_action() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    // Same precedence through the _no_semi expression twins used in actions.
    let m = common::parse_machine(
        r#"
    MACHINE test
    VARIABLES
        x a b c
    EVENTS
        EVENT update
        THEN
            @act1 x ≔ a ↦ b ↔ c
        END
    END
    "#,
    );
    let event = &m.events[0];
    match &event.actions[0].action.kind {
        ActionKind::Assignment { assignments } => match &assignments[0].1.kind {
            ExpressionKind::Binary { op, right, .. } => {
                assert_eq!(*op, BinaryOp::Maplet);
                assert!(matches!(
                    &right.kind,
                    ExpressionKind::Binary {
                        op: BinaryOp::Relation,
                        ..
                    }
                ));
            }
            other => panic!("Expected Maplet, got {:?}", other),
        },
        other => panic!("Expected Assignment, got {:?}", other),
    }
}

test_binary_op!(
    test_total_function,
    "S, T, f",
    "f = S --> T",
    BinaryOp::TotalFunction
);
test_binary_op!(
    test_partial_function,
    "S, T, f",
    "f = S +-> T",
    BinaryOp::PartialFunction
);
test_binary_op!(
    test_relation_type,
    "S, T, r",
    "r = S <-> T",
    BinaryOp::Relation
);
test_binary_op!(
    test_domain_restriction,
    "S, f, r",
    "r = S <| f",
    BinaryOp::DomainRestriction
);
test_binary_op!(
    test_range_restriction,
    "f, S, r",
    "r = f |> S",
    BinaryOp::RangeRestriction
);
test_binary_op!(
    test_domain_subtraction,
    "S, f, r",
    "r = S <<| f",
    BinaryOp::DomainSubtraction
);
test_binary_op!(
    test_range_subtraction,
    "f, S, r",
    "r = f |>> S",
    BinaryOp::RangeSubtraction
);
test_binary_op!(test_overwrite, "f, g, r", "r = f <+ g", BinaryOp::Overwrite);
test_binary_op!(
    test_overwrite_pua,
    "f, g, r",
    "r = f \u{E103} g",
    BinaryOp::Overwrite
);
test_binary_op!(test_exponent, "a, b, r", "r = a ^ b", BinaryOp::Exponent);

/// Per spec §3.3.6: exponent binds tighter than additive and multiplicative.
/// `2 ^ 3 + 4` must parse as `(2 ^ 3) + 4`, not `2 ^ (3 + 4)`.
#[test]
fn test_exponent_precedence_vs_additive() {
    use rossi::ast::expression::BinaryOp;

    // 2 ^ 3 + 4 should be (2^3) + 4, i.e. Add at the top
    let source = common::axiom_context("r", "r = 2 ^ 3 + 4");
    let rhs = common::parse_axiom_rhs(&source);
    assert!(
        matches!(
            &rhs.kind,
            ExpressionKind::Binary {
                op: BinaryOp::Add,
                left,
                right,
            } if matches!(
                &left.kind,
                ExpressionKind::Binary { op: BinaryOp::Exponent, .. }
            ) && matches!(&right.kind, ExpressionKind::Integer(4))
        ),
        "2 ^ 3 + 4 should parse as (2^3)+4, got {:?}",
        rhs
    );
}

/// `a * b ^ c` must parse as `a * (b ^ c)`, not `(a * b) ^ c`.
#[test]
fn test_exponent_precedence_vs_multiplicative() {
    use rossi::ast::expression::BinaryOp;

    let source = common::axiom_context("a, b, c, r", "r = a * b ^ c");
    let rhs = common::parse_axiom_rhs(&source);
    assert!(
        matches!(
            &rhs.kind,
            ExpressionKind::Binary {
                op: BinaryOp::Multiply,
                left,
                right,
            } if matches!(&left.kind, ExpressionKind::Identifier(id) if id == "a")
              && matches!(&right.kind, ExpressionKind::Binary { op: BinaryOp::Exponent, .. })
        ),
        "a * b ^ c should parse as a*(b^c), got {:?}",
        rhs
    );
}

test_binary_op!(
    test_direct_product,
    "f, g, r",
    "r = f >< g",
    BinaryOp::DirectProduct
);

#[test]
fn test_multiply_vs_cartesian_product() {
    use rossi::ExpressionKind;
    use rossi::ast::expression::BinaryOp;

    // ASCII "*" should parse as Multiply
    let source = common::axiom_context("a, b, r", "r = a * b");
    let rhs = common::parse_axiom_rhs(&source);
    assert!(
        matches!(
            &rhs.kind,
            ExpressionKind::Binary {
                op: BinaryOp::Multiply,
                ..
            }
        ),
        "Single * should parse as Multiply, got {:?}",
        rhs
    );

    // ASCII "**" should parse as CartesianProduct
    let source = common::axiom_context("S, T, r", "r = S ** T");
    let rhs = common::parse_axiom_rhs(&source);
    assert!(
        matches!(
            &rhs.kind,
            ExpressionKind::Binary {
                op: BinaryOp::CartesianProduct,
                ..
            }
        ),
        "Double ** should parse as CartesianProduct, got {:?}",
        rhs
    );

    // Unicode "×" should parse as CartesianProduct
    let source = common::axiom_context("S, T, r", "r = S \u{00D7} T");
    let rhs = common::parse_axiom_rhs(&source);
    assert!(
        matches!(
            &rhs.kind,
            ExpressionKind::Binary {
                op: BinaryOp::CartesianProduct,
                ..
            }
        ),
        "Unicode × should parse as CartesianProduct, got {:?}",
        rhs
    );
}

// ASCII and Unicode type-set tokens parse as the builtin type sets, not as
// identifiers.
#[test_case::test_case("NAT1", ExpressionKind::Naturals1 ; "nat1_ascii")]
#[test_case::test_case("\u{2115}1", ExpressionKind::Naturals1 ; "nat1_unicode")]
#[test_case::test_case("INT", ExpressionKind::Integers ; "int_ascii")]
#[test_case::test_case("\u{2124}", ExpressionKind::Integers ; "int_unicode")]
#[test_case::test_case("NAT", ExpressionKind::Naturals ; "nat_ascii")]
fn type_set_token_parses_as_type_set(token: &str, expected: ExpressionKind) {
    let source = common::invariant_machine("x", &format!("x ∈ {token}"));
    let m = common::parse_machine(&source);
    let rossi::PredicateKind::Comparison { right, .. } = &m.invariants[0].predicate.kind else {
        panic!("Expected Comparison predicate");
    };
    assert_eq!(
        *right,
        expected.into(),
        "{token} should parse as the builtin type set, not Identifier"
    );
}

// ASCII type-set spellings are exact-case (uppercase NAT1/INT); the lowercase
// form is an ordinary identifier, not the type set.
#[test_case::test_case("nat1", "Naturals1" ; "nat1")]
#[test_case::test_case("int", "Integers" ; "int")]
fn lowercase_type_keyword_is_identifier(word: &str, type_set: &str) {
    use rossi::ExpressionKind;

    let source = common::invariant_machine("x", &format!("x ∈ {word}"));
    let m = common::parse_machine(&source);
    let rossi::PredicateKind::Comparison { right, .. } = &m.invariants[0].predicate.kind else {
        panic!("Expected Comparison predicate");
    };
    assert_eq!(
        *right,
        ExpressionKind::Identifier(word.to_string()).into(),
        "lowercase {word} is an ordinary identifier, not {type_set}"
    );
}

#[test]
fn test_nat1_int_roundtrip() {
    // Test NAT1 roundtrip via Unicode
    common::assert_roundtrip(
        r#"
    MACHINE test
    VARIABLES
        x
    INVARIANTS
        @inv1 x ∈ NAT1
    END
    "#,
    );

    // Test INT roundtrip via ASCII
    common::assert_roundtrip_ascii(
        r#"
    MACHINE test
    VARIABLES
        x
    INVARIANTS
        @inv1 x ∈ INT
    END
    "#,
    );
}

#[test]
fn test_negation_in_conjunction() {
    use rossi::PredicateKind;
    use rossi::ast::predicate::LogicalOp;

    let m = common::parse_machine(
        r#"
    MACHINE test
    VARIABLES
        x y
    INVARIANTS
        @inv1 ¬(x > 0) ∧ y > 0
    END
    "#,
    );
    let pred = &m.invariants[0].predicate;
    match &pred.kind {
        PredicateKind::Logical { op, left, right } => {
            assert_eq!(*op, LogicalOp::And);
            assert!(matches!(left.as_ref().kind, PredicateKind::Not(_)));
            assert!(matches!(
                right.as_ref().kind,
                PredicateKind::Comparison { .. }
            ));
        }
        other => panic!("Expected Logical predicate, got {:?}", other),
    }
}

// --- becomes-such-that: Unicode :∣ and ASCII :| produce the same AST ----------

#[test]
fn test_becomes_such_that_unicode_and_ascii_same_ast() {
    let source_unicode = r#"
    MACHINE test
    EVENTS
        EVENT INITIALISATION
        THEN
            @act1 x :∣ x > 0
        END
    END
    "#;
    let source_ascii = r#"
    MACHINE test
    EVENTS
        EVENT INITIALISATION
        THEN
            @act1 x :| x > 0
        END
    END
    "#;

    let result_unicode = parse(source_unicode);
    assert!(
        result_unicode.is_ok(),
        "Unicode :∣ should parse: {:?}",
        result_unicode.err()
    );
    let result_ascii = parse(source_ascii);
    assert!(
        result_ascii.is_ok(),
        "ASCII :| should parse: {:?}",
        result_ascii.err()
    );

    // Both should produce identical AST (clear spans since byte offsets differ)
    let mut component_unicode = result_unicode.unwrap();
    let mut component_ascii = result_ascii.unwrap();
    common::clear_spans(&mut component_unicode);
    common::clear_spans(&mut component_ascii);
    assert_eq!(
        component_unicode, component_ascii,
        "Unicode :∣ and ASCII :| should produce the same AST"
    );
}

// ============================================================================
// Expression precedence tests (spec §3.3.4 Table 3.1)
// ============================================================================

use rossi::ast::expression::BinaryOp;

#[test]
fn test_range_cartesian_product() {
    // 1‥2 × 1‥3 should parse as (1‥2) × (1‥3), not 1 ‥ (2×1) ‥ 3
    let source = common::axiom_context("S", "S = 1‥2 × 1‥3");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary {
            op: BinaryOp::CartesianProduct,
            left,
            right,
        } => {
            assert!(
                matches!(
                    left.as_ref().kind,
                    ExpressionKind::Binary {
                        op: BinaryOp::Range,
                        ..
                    }
                ),
                "Left should be Range, got {:?}",
                left
            );
            assert!(
                matches!(
                    right.as_ref().kind,
                    ExpressionKind::Binary {
                        op: BinaryOp::Range,
                        ..
                    }
                ),
                "Right should be Range, got {:?}",
                right
            );
        }
        other => panic!("Expected CartesianProduct of two Ranges, got {:?}", other),
    }
}

#[test]
fn test_arithmetic_before_range() {
    // a + b .. c should parse as (a + b) .. c
    let source = common::axiom_context("a, b, c, S", "S = a + b .. c");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary {
            op: BinaryOp::Range,
            left,
            ..
        } => {
            assert!(
                matches!(
                    left.as_ref().kind,
                    ExpressionKind::Binary {
                        op: BinaryOp::Add,
                        ..
                    }
                ),
                "Left of Range should be Add, got {:?}",
                left
            );
        }
        other => panic!("Expected Range with Add left, got {:?}", other),
    }
}

#[test]
fn test_range_before_union() {
    // a .. b ∪ C should parse as (a .. b) ∪ C
    let source = common::axiom_context("a, b, C, S", "S = a .. b ∪ C");
    let rhs = common::parse_axiom_rhs(&source);
    match &rhs.kind {
        ExpressionKind::Binary {
            op: BinaryOp::Union,
            left,
            ..
        } => {
            assert!(
                matches!(
                    left.as_ref().kind,
                    ExpressionKind::Binary {
                        op: BinaryOp::Range,
                        ..
                    }
                ),
                "Left of Union should be Range, got {:?}",
                left
            );
        }
        other => panic!("Expected Union with Range left, got {:?}", other),
    }
}

// ── TRUE / FALSE in expressions vs predicate constants ──────────────

// TRUE/FALSE in expression position (here: element of a set) parse as
// expressions, not as the predicate constants.
#[test_case::test_case("TRUE", ExpressionKind::True ; "true_literal")]
#[test_case::test_case("FALSE", ExpressionKind::False ; "false_literal")]
fn bool_literal_in_set(token: &str, expected: ExpressionKind) {
    use rossi::PredicateKind;
    use rossi::ast::predicate::ComparisonOp;
    let source = format!("CONTEXT test\nAXIOMS\n    @axm1 {token} ∈ {{queue_1, queue_2}}\nEND\n");
    let ctx = common::parse_context(&source);
    match &ctx.axioms[0].predicate.kind {
        PredicateKind::Comparison {
            op: ComparisonOp::In,
            left,
            ..
        } => {
            assert_eq!(left.kind, expected, "for {token}");
        }
        other => panic!("Expected {token} ∈ comparison, got {other:?}"),
    }
}

// The bare ⊤/⊥ constants parse as predicates.
#[test_case::test_case("⊤", rossi::PredicateKind::True ; "true_constant")]
#[test_case::test_case("⊥", rossi::PredicateKind::False ; "false_constant")]
fn bare_bool_predicate(axiom_body: &str, expected: rossi::PredicateKind) {
    let source = format!("CONTEXT test\nAXIOMS\n    @axm1 {axiom_body}\nEND\n");
    let ctx = common::parse_context(&source);
    assert_eq!(ctx.axioms[0].predicate.kind, expected, "for {axiom_body}");
}

// TRUE parses as an expression on either side of `=` — the RHS position
// (immediately before END) is the token-boundary position issue #30 was about.
#[test_case::test_case("TRUE = x", true ; "true_on_lhs")]
#[test_case::test_case("x = TRUE", false ; "true_on_rhs")]
fn test_true_eq_comparison(axiom_body: &str, true_on_left: bool) {
    use rossi::PredicateKind;
    use rossi::ast::predicate::ComparisonOp;
    let source = common::axiom_context("x", axiom_body);
    let ctx = common::parse_context(&source);
    match &ctx.axioms[0].predicate.kind {
        PredicateKind::Comparison {
            op: ComparisonOp::Equal,
            left,
            right,
        } => {
            let operand = if true_on_left { left } else { right };
            assert!(
                matches!(operand.kind, ExpressionKind::True),
                "Expected Expression::True in {axiom_body:?}, got {:?}",
                operand
            );
        }
        other => panic!("Expected TRUE equality comparison, got {:?}", other),
    }
}

// ===== Postfix function update: f{x ↦ y} == f <+ {x ↦ y} =====
//
// Rodin's parser accepts this compact form (well-formed under its
// FormulaFactory.OVR tag); our grammar lowers it to the same AST as the
// explicit <+ form so consumers don't need to handle a new variant. The
// canonical static-checker emission uses U+E103.

#[test]
fn test_postfix_function_update_lowers_to_overwrite() {
    let postfix = parse_expression_str("f{x ↦ y}").expect("postfix update parses");
    let explicit = parse_expression_str("f <+ {x ↦ y}").expect("explicit overwrite parses");
    assert_eq!(postfix, explicit);

    let postfix = parse_expression_str("f{x ↦ y, a ↦ b}").expect("multi-element postfix parses");
    let explicit =
        parse_expression_str("f <+ {x ↦ y, a ↦ b}").expect("multi-element explicit parses");
    assert_eq!(postfix, explicit);
}

#[test]
fn test_postfix_function_update_in_action() {
    let action = parse_action_str("currentFloor ≔ currentFloor{c ↦ f}").expect("action parses");
    let equivalent = parse_action_str("currentFloor ≔ currentFloor <+ {c ↦ f}").expect("explicit");
    assert_eq!(action, equivalent);
    match action.kind {
        ActionKind::Assignment { ref assignments } => {
            assert_eq!(assignments.len(), 1);
            assert_eq!(assignments[0].0, "currentFloor");
        }
        other => panic!("Expected Assignment, got {:?}", other),
    }
}

#[test]
fn test_postfix_function_update_set_enumeration_unaffected() {
    // A bare set enumeration is still set_enumeration — only postfix
    // application after a primary_expr triggers the new branch.
    let bare = parse_expression_str("{x ↦ y}").expect("bare set enum parses");
    match bare.kind {
        ExpressionKind::SetEnumeration(_) => {}
        other => panic!("Expected SetEnumeration, got {:?}", other),
    }
}

// Regression: `parse_expression` and `parse_predicate` recurse through every
// precedence-wrapper rule on the way down, which previously consumed enough
// stack on this file-system invariant to overflow a 2 MB test thread.
// `parse_expression` and `parse_predicate` now unwrap single-child wrappers
// in a loop, so this should fit comfortably in 1 MB.
#[test]
fn test_deep_predicate_fits_in_small_stack() {
    use rossi::parse_predicate_str;
    let input = "C ∖ {x ↦ y ∣ y ∈ dom(f(x))}[C] ≠ ∅";
    let s: String = input.into();
    let parsed = std::thread::Builder::new()
        .stack_size(1024 * 1024) // 1 MB — was failing at 2 MB before the fix
        .spawn(move || parse_predicate_str(&s).is_ok())
        .unwrap()
        .join()
        .unwrap_or(false);
    assert!(parsed, "file-system invariant must parse on a 1 MB stack");
}

// ===== Surjection alias spellings parse at the grammar level =====
//
// `+->>`/`-->>` are accepted alternative ASCII input spellings for the
// surjection arrows (Rodin's keyboard). Eager input converts them to ⤀/↠
// before the parser sees them, but raw text (pasted, or with eager input off)
// must still parse — and as the *surjection*, not the `+->`/`-->` function
// arrow they extend with a dangling `>`. These pin the `op_partial_surj` /
// `op_total_surj` grammar alternatives so a future reorder can't regress them.

fn binary_op_of(src: &str) -> rossi::ast::expression::BinaryOp {
    match parse_expression_str(src)
        .unwrap_or_else(|e| panic!("expected `{src}` to parse, got: {e}"))
        .kind
    {
        ExpressionKind::Binary { op, .. } => op,
        other => panic!("expected `{src}` to be a binary expression, got: {other:?}"),
    }
}

#[test]
fn test_surjection_alias_spellings_parse_as_surjections() {
    use rossi::ast::expression::BinaryOp;
    assert_eq!(binary_op_of("S +->> T"), BinaryOp::PartialSurjection);
    assert_eq!(binary_op_of("S -->> T"), BinaryOp::TotalSurjection);
    // The canonical forms still parse identically.
    assert_eq!(binary_op_of("S +>> T"), BinaryOp::PartialSurjection);
    assert_eq!(binary_op_of("S ->> T"), BinaryOp::TotalSurjection);
    // …and the shorter function arrows they extend are unaffected (no
    // dangling `>` left behind by a greedy surjection match).
    assert_eq!(binary_op_of("S +-> T"), BinaryOp::PartialFunction);
    assert_eq!(binary_op_of("S --> T"), BinaryOp::TotalFunction);
}

#[test]
fn test_relation_arrow_and_typing_operator_spellings() {
    use rossi::ast::expression::BinaryOp;
    assert_eq!(binary_op_of("A <<-> B"), BinaryOp::TotalRelation);
    assert_eq!(binary_op_of("A <->> B"), BinaryOp::SurjectiveRelation);
    assert_eq!(binary_op_of("A <<->> B"), BinaryOp::TotalSurjectiveRelation);
    // Both spellings of the oftype typing operator.
    assert_eq!(binary_op_of("\u{2115} oftype \u{2124}"), BinaryOp::OfType);
    assert_eq!(binary_op_of("\u{2115} \u{2982} \u{2124}"), BinaryOp::OfType);
    // Regression (d581fd2): `,,` is a maplet spelling, not the empty set.
    assert_eq!(binary_op_of("x ,, y"), BinaryOp::Maplet);
}

#[test]
fn test_unicode_whitespace_matches_rodin() {
    // Rodin's math lexer treats any Unicode space separator as whitespace
    // (LexicalClass.isWhitespace + FormulaFactory.isEventBWhiteSpace), including
    // the non-breaking spaces Java's Character.isWhitespace omits. rossi's
    // WHITESPACE rule mirrors that set, so a predicate separated by such spaces
    // parses identically to the ASCII-space form. Real Rodin XML in the wild puts
    // U+00A0 around operators like `=` and `≤`, which Rodin accepts.
    let ascii = rossi::parse_predicate_str("sense_ev = TRUE ⇒ ct ≤ st")
        .expect("ASCII-spaced predicate should parse");

    // U+00A0 NO-BREAK SPACE separating the operands and operators.
    let nbsp = rossi::parse_predicate_str("sense_ev\u{a0}=\u{a0}TRUE ⇒ ct\u{a0}≤\u{a0}st")
        .expect("U+00A0-separated predicate should parse");
    assert_eq!(
        nbsp, ascii,
        "U+00A0 must be whitespace, same AST as ASCII spaces"
    );

    // U+2007 FIGURE SPACE — another non-breaking Zs space Java excludes but Rodin
    // accepts; confirms we matched the category, not just the one codepoint.
    let figure = rossi::parse_predicate_str("sense_ev\u{2007}=\u{2007}TRUE ⇒ ct ≤ st")
        .expect("U+2007-separated predicate should parse");
    assert_eq!(
        figure, ascii,
        "U+2007 must be whitespace, same AST as ASCII spaces"
    );

    // Negative parity: U+200B ZERO WIDTH SPACE is category Cf, not a space
    // separator — Rodin does NOT treat it as whitespace, so neither do we. It
    // must fail rather than silently glue tokens together.
    assert!(
        rossi::parse_predicate_str("sense_ev\u{200b}=\u{200b}TRUE").is_err(),
        "U+200B is not whitespace in Rodin; it must not parse as a separator"
    );
}

#[test]
fn test_label_terminates_on_unicode_whitespace() {
    // A label is "@" then non-whitespace up to the next whitespace. The grammar's
    // whitespace set now includes U+00A0, and the `label_text` rule references
    // WHITESPACE, so a label followed by a U+00A0 must terminate at it — not
    // swallow the following predicate into the label. With a U+00A0 between the
    // label and the predicate, the label is still `axm1` and `1 = 1` parses as
    // the axiom predicate.
    let ctx = common::parse_context("CONTEXT c\nAXIOMS\n@axm1\u{a0}1 = 1\nEND\n");
    assert_eq!(ctx.axioms.len(), 1);
    assert_eq!(ctx.axioms[0].label.as_deref(), Some("axm1"));
}

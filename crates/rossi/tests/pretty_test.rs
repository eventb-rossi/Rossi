mod common;

use rossi::ast::expression::{AtomicBuiltinKind, BinaryOp, UnaryOp};
use rossi::ast::predicate::{ComparisonOp, LogicalOp};
use rossi::*;
use test_case::test_case;

// ============================================================================
// Pretty-print assertion tests (individual — custom assertions)
// ============================================================================

#[test]
fn test_pretty_print_inverse_operator() {
    // ASCII `~` input round-trips: Unicode mode emits ∼ (U+223C), ASCII mode
    // emits ~ (U+007E).
    let source = common::axiom_context("f, r", "r = f~");
    let component = parse(&source).expect("Failed to parse ASCII ~ inverse");

    let unicode = to_string(&component);
    assert!(
        unicode.contains("f\u{223C}"),
        "Unicode output should use ∼, got: {unicode}"
    );

    let ascii = to_string_ascii(&component);
    assert!(
        ascii.contains("f~"),
        "ASCII output should use ~, got: {ascii}"
    );
    assert!(
        !ascii.contains('\u{223C}'),
        "ASCII output must not contain U+223C"
    );
}

#[test]
fn test_pretty_print_cartesian_product_left_associative() {
    // `×` is left-associative: Rodin renders a left-nested chain bare and
    // only parenthesizes a right-nested child. Regression test for the
    // shared `op_info::set_ops_compatible` table (a missing `(×, ×)` entry
    // made `rossi fmt` emit `(ℤ × ℤ) × ℤ`, diverging from Rodin).
    let left_nested = common::axiom_context("S", "S = ℤ × ℤ × ℤ");
    let out = to_string(&parse(&left_nested).expect("parse left-nested ×"));
    assert!(
        out.contains("ℤ × ℤ × ℤ") && !out.contains("(ℤ × ℤ)"),
        "left-nested × must print bare, got: {out}"
    );

    let right_nested = common::axiom_context("S", "S = ℤ × (ℤ × ℤ)");
    let out = to_string(&parse(&right_nested).expect("parse right-nested ×"));
    assert!(
        out.contains("ℤ × (ℤ × ℤ)"),
        "right-nested × must keep its parentheses, got: {out}"
    );
}

#[test]
fn test_pretty_print_context_with_all_clauses() {
    let source = r#"CONTEXT test_ctx
EXTENDS base_ctx
SETS
    STATUS
CONSTANTS
    max_value
AXIOMS
    @axm1 max_value = 100
    @axm2 max_value > 0
    @thm1 theorem max_value >= 0
END
"#;

    let component = parse(source).expect("Failed to parse");
    let output = to_string(&component);

    assert!(output.contains("CONTEXT test_ctx"));
    assert!(output.contains("EXTENDS"));
    assert!(output.contains("base_ctx"));
    assert!(output.contains("SETS"));
    assert!(output.contains("STATUS"));
    assert!(output.contains("CONSTANTS"));
    assert!(output.contains("max_value"));
    assert!(output.contains("AXIOMS"));
    assert!(output.contains("@axm1"));
    assert!(
        !output.contains("THEOREMS"),
        "Output should not contain THEOREMS keyword — theorems are inline within AXIOMS"
    );
    assert!(output.contains("@thm1"));
    assert!(output.contains("theorem"));
    assert!(output.contains("END"));
}

#[test]
fn test_pretty_print_convergent_event() {
    let source = r#"MACHINE test
VARIABLES
    x
VARIANT
    x
EVENTS
    EVENT INITIALISATION
    THEN
        x := 10
    END

    EVENT decrement
    STATUS convergent
    WHERE
        @grd1 x > 0
    THEN
        x := x - 1
    END
END
"#;

    let component = parse(source).expect("Failed to parse");
    let output = to_string(&component);

    assert!(output.contains("VARIANT"));
    assert!(output.contains("EVENT decrement"));
    assert!(output.contains("convergent EVENT decrement"));
}

#[test]
fn test_pretty_print_parallel_assignment_keeps_all_pairs() {
    let action = parse_action_str("x, y := 1, 2").expect("parallel assignment parses");
    assert_eq!(PrettyPrinter::new().print_action(&action), "x, y ≔ 1, 2");
    assert_eq!(PrettyPrinter::ascii().print_action(&action), "x, y := 1, 2");
}

#[test]
fn rodin_canonical_binary_spacing_is_exhaustive() {
    use rossi::ast::expression::BinaryOp;

    let cases = [
        (BinaryOp::Add, true),
        (BinaryOp::Subtract, false),
        (BinaryOp::Multiply, true),
        (BinaryOp::Divide, false),
        (BinaryOp::Modulo, false),
        (BinaryOp::Exponent, false),
        (BinaryOp::Range, false),
        (BinaryOp::Union, true),
        (BinaryOp::Intersection, true),
        (BinaryOp::Difference, false),
        (BinaryOp::CartesianProduct, true),
        (BinaryOp::Relation, false),
        (BinaryOp::TotalRelation, false),
        (BinaryOp::SurjectiveRelation, false),
        (BinaryOp::TotalSurjectiveRelation, false),
        (BinaryOp::TotalFunction, false),
        (BinaryOp::PartialFunction, false),
        (BinaryOp::TotalInjection, false),
        (BinaryOp::PartialInjection, false),
        (BinaryOp::TotalSurjection, false),
        (BinaryOp::PartialSurjection, false),
        (BinaryOp::Bijection, false),
        (BinaryOp::Composition, false),
        (BinaryOp::Semicolon, false),
        (BinaryOp::DomainRestriction, false),
        (BinaryOp::DomainSubtraction, false),
        (BinaryOp::RangeRestriction, false),
        (BinaryOp::RangeSubtraction, false),
        (BinaryOp::Overwrite, true),
        (BinaryOp::DirectProduct, false),
        (BinaryOp::ParallelProduct, false),
        (BinaryOp::OfType, false),
        (BinaryOp::Maplet, false),
    ];
    let printer = PrettyPrinter::rodin_canonical();

    for (op, tight) in cases {
        let expression: Expression = ExpressionKind::Binary {
            op,
            left: Box::new(ExpressionKind::Identifier("a".into()).into()),
            right: Box::new(ExpressionKind::Identifier("b".into()).into()),
        }
        .into();
        let operator = operators::spell(operators::binary_op_id(op), true);
        let separator = if tight { "" } else { " " };
        assert_eq!(
            printer.print_expression(&expression),
            format!("a{separator}{operator}{separator}b"),
            "wrong Rodin spacing for {op:?}"
        );
    }
}

#[test]
fn rodin_canonical_tightens_comparisons_and_logical_operators() {
    use rossi::ast::predicate::{ComparisonOp, LogicalOp};

    let comparison_ops = [
        ComparisonOp::Equal,
        ComparisonOp::NotEqual,
        ComparisonOp::LessThan,
        ComparisonOp::LessEqual,
        ComparisonOp::GreaterThan,
        ComparisonOp::GreaterEqual,
        ComparisonOp::In,
        ComparisonOp::NotIn,
        ComparisonOp::Subset,
        ComparisonOp::SubsetStrict,
        ComparisonOp::NotSubset,
        ComparisonOp::NotSubsetStrict,
    ];
    let printer = PrettyPrinter::rodin_canonical();

    for op in comparison_ops {
        let predicate: Predicate = PredicateKind::Comparison {
            op,
            left: ExpressionKind::Identifier("a".into()).into(),
            right: ExpressionKind::Identifier("b".into()).into(),
        }
        .into();
        let operator = operators::spell(operators::comparison_op_id(op), true);
        assert_eq!(
            printer.print_predicate(&predicate),
            format!("a{operator}b"),
            "wrong Rodin spacing for {op:?}"
        );
    }

    let comparison = |left: &str, right: &str| -> Predicate {
        PredicateKind::Comparison {
            op: ComparisonOp::Equal,
            left: ExpressionKind::Identifier(left.into()).into(),
            right: ExpressionKind::Identifier(right.into()).into(),
        }
        .into()
    };
    for op in [
        LogicalOp::And,
        LogicalOp::Or,
        LogicalOp::Implies,
        LogicalOp::Equivalent,
    ] {
        let predicate: Predicate = PredicateKind::Logical {
            op,
            left: Box::new(comparison("a", "b")),
            right: Box::new(comparison("c", "d")),
        }
        .into();
        let operator = operators::spell(operators::logical_op_id(op), true);
        assert_eq!(
            printer.print_predicate(&predicate),
            format!("a=b{operator}c=d"),
            "wrong Rodin spacing for {op:?}"
        );
    }
}

#[test]
fn rodin_canonical_ascii_keeps_word_operator_boundaries() {
    let predicate = parse_predicate_str("a = b or c = d").expect("predicate parses");
    let printer = PrettyPrinter::ascii().with_formula_spacing(FormulaSpacing::RodinCanonical);
    let printed = printer.print_predicate(&predicate);

    assert_eq!(printed, "a=b or c=d");
    assert_eq!(
        parse_predicate_str(&printed).expect("printed predicate reparses"),
        predicate
    );
}

#[test]
fn rodin_canonical_preserves_root_specific_type_ascription_spacing() {
    let printer = PrettyPrinter::rodin_canonical();
    let expression = parse_expression_str("a ⦂ b").expect("expression parses");
    let predicate = parse_predicate_str("a ⦂ b = c").expect("predicate parses");
    let bool_expression = parse_expression_str("bool(a ⦂ b = c)").expect("bool parses");
    let action = parse_action_str("x ≔ a ⦂ b").expect("action parses");

    assert_eq!(printer.print_expression(&expression), "a ⦂ b");
    assert_eq!(printer.print_predicate(&predicate), "a⦂b=c");
    assert_eq!(printer.print_expression(&bool_expression), "bool(a ⦂ b=c)");
    assert_eq!(printer.print_action(&action), "x ≔ a ⦂ b");
}

#[test]
fn rodin_canonical_tightens_comma_separated_formula_lists() {
    let printer = PrettyPrinter::rodin_canonical();
    let expression = parse_expression_str("{1, 2, 3}").expect("enumeration parses");
    let predicate = parse_predicate_str("∀x⦂ℤ, y⦂ℤ · p(x, y)").expect("predicate parses");
    let action = parse_action_str("x, y ≔ 1, 2").expect("action parses");

    assert_eq!(printer.print_expression(&expression), "{1,2,3}");
    assert_eq!(printer.print_predicate(&predicate), "∀x⦂ℤ,y⦂ℤ·p(x,y)");
    assert_eq!(printer.print_action(&action), "x,y ≔ 1,2");

    assert_eq!(
        PrettyPrinter::new().print_expression(&expression),
        "{1, 2, 3}"
    );
    assert_eq!(PrettyPrinter::new().print_action(&action), "x, y ≔ 1, 2");
}

#[test]
fn test_pretty_print_sees_and_refines() {
    let source = r#"MACHINE refined
REFINES
    abstract
SEES
    ctx1
    ctx2
END
"#;

    let component = parse(source).expect("Failed to parse");
    let output = to_string(&component);

    assert!(output.contains("REFINES"));
    assert!(output.contains("abstract"));
    assert!(output.contains("SEES"));
    assert!(output.contains("ctx1"));
    assert!(output.contains("ctx2"));
}

#[test]
fn test_pretty_printer_custom_indent() {
    let source = r#"CONTEXT test
SETS
    STATUS
END
"#;

    let component = parse(source).expect("Failed to parse");
    let printer = PrettyPrinter::new().with_indent("  ".to_string());
    let output = printer.print_component(&component);

    assert!(output.contains("  STATUS"));
}

#[test]
fn test_pretty_print_machine_no_events() {
    let source = r#"MACHINE simple
VARIABLES
    x
INVARIANTS
    @inv1 x >= 0
END
"#;

    let component = parse(source).expect("Failed to parse");
    let output = to_string(&component);

    assert!(output.contains("MACHINE simple"));
    assert!(output.contains("VARIABLES"));
    assert!(output.contains("INVARIANTS"));
    assert!(
        !output.contains("EVENTS"),
        "Output should not contain EVENTS when there are no events"
    );
    assert!(output.contains("END"));
}

// ============================================================================
// Precedence-aware parenthesization tests (parametrized — AST construction)
//
// Each row pins the canonical *minimal* parenthesization, which the roundtrip
// properties cannot check (over-parenthesized output also roundtrips). The
// shared body additionally reparses the printed form back to the same AST, so
// every canonical form is also proven parser-stable.
// ============================================================================

fn id(name: &str) -> Expression {
    Expression::identifier(name)
}

fn bin(op: BinaryOp, left: Expression, right: Expression) -> Expression {
    ExpressionKind::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
    .into()
}

fn un(op: UnaryOp, operand: Expression) -> Expression {
    ExpressionKind::Unary {
        op,
        operand: Box::new(operand),
    }
    .into()
}

/// `<name> > 0` — comparison leaf for the logical-operator rows.
fn gt0(name: &str) -> Predicate {
    PredicateKind::Comparison {
        op: ComparisonOp::GreaterThan,
        left: id(name),
        right: ExpressionKind::Integer(0).into(),
    }
    .into()
}

fn logic(op: LogicalOp, left: Predicate, right: Predicate) -> Predicate {
    PredicateKind::Logical {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
    .into()
}

// (a + b) + c prints flat: left child, same precedence, left-associative.
#[test_case(
    bin(BinaryOp::Add, bin(BinaryOp::Add, id("a"), id("b")), id("c")),
    "a + b + c";
    "same_prec_left_assoc_no_parens"
)]
// a + (b + c) keeps parens: right child of a left-associative operator.
#[test_case(
    bin(BinaryOp::Add, id("a"), bin(BinaryOp::Add, id("b"), id("c"))),
    "a + (b + c)";
    "same_prec_right_child_parens"
)]
// a + b ∗ c prints flat: multiply is higher precedence. (∗ ASTERISK OPERATOR)
#[test_case(
    bin(BinaryOp::Add, id("a"), bin(BinaryOp::Multiply, id("b"), id("c"))),
    "a + b \u{2217} c";
    "higher_prec_child_no_parens"
)]
// (a + b) ∗ c keeps parens: add is lower precedence than multiply.
#[test_case(
    bin(BinaryOp::Multiply, bin(BinaryOp::Add, id("a"), id("b")), id("c")),
    "(a + b) \u{2217} c";
    "lower_prec_child_parens"
)]
// a − b + c prints flat: left child, same precedence, left-assoc. (− MINUS SIGN)
#[test_case(
    bin(BinaryOp::Add, bin(BinaryOp::Subtract, id("a"), id("b")), id("c")),
    "a \u{2212} b + c";
    "mixed_same_prec_left_child"
)]
// a + (b − c) keeps parens: right child, same precedence, left-assoc.
#[test_case(
    bin(BinaryOp::Add, id("a"), bin(BinaryOp::Subtract, id("b"), id("c"))),
    "a + (b \u{2212} c)";
    "mixed_same_prec_right_child"
)]
// a ↦ (b ↦ c): right child is itself a Maplet, so keep parens
// (left-associative — same-level Maplet on the right is non-default grouping).
#[test_case(
    bin(BinaryOp::Maplet, id("a"), bin(BinaryOp::Maplet, id("b"), id("c"))),
    "a \u{21A6} (b \u{21A6} c)";
    "maplet_right_grouped_parens"
)]
// (a ↦ b) ↦ c: the natural left-associative grouping
// (`a ↦ b ↦ c = (a ↦ b) ↦ c` per spec p.18), so emit flat.
#[test_case(
    bin(BinaryOp::Maplet, bin(BinaryOp::Maplet, id("a"), id("b")), id("c")),
    "a \u{21A6} b \u{21A6} c";
    "maplet_left_grouped_no_parens"
)]
// a ↦ (b ↔ c): arrows bind tighter than maplet (kernel_lang Table 3.1;
// regression context: c3e3cae), so this is the natural grouping — emit flat.
#[test_case(
    bin(BinaryOp::Maplet, id("a"), bin(BinaryOp::Relation, id("b"), id("c"))),
    "a \u{21A6} b \u{2194} c";
    "arrow_inside_maplet_no_parens"
)]
// (a ↦ b) ↔ c: maplet binds looser than the arrow (kernel_lang Table 3.1;
// regression context: c3e3cae) — dropping the parens would re-bind as
// a ↦ (b ↔ c), a different AST.
#[test_case(
    bin(BinaryOp::Relation, bin(BinaryOp::Maplet, id("a"), id("b")), id("c")),
    "(a \u{21A6} b) \u{2194} c";
    "maplet_inside_arrow_parens"
)]
// (S ∪ T) ∖ U — Union and Difference are in different Camille compatibility
// classes, so parens are required.
#[test_case(
    bin(BinaryOp::Difference, bin(BinaryOp::Union, id("S"), id("T")), id("U")),
    "(S ∪ T) ∖ U";
    "union_difference_incompatible"
)]
// S ∖ (T ∖ U) — Difference is Camille class 0, incompatible even with itself.
#[test_case(
    bin(
        BinaryOp::Difference,
        id("S"),
        bin(BinaryOp::Difference, id("T"), id("U"))
    ),
    "S ∖ (T ∖ U)";
    "difference_self_incompatible"
)]
// (S ∖ T) ∖ U — per Table 3.2 the ∖ row is completely empty, so parens are
// always required, even for the left child.
#[test_case(
    bin(
        BinaryOp::Difference,
        bin(BinaryOp::Difference, id("S"), id("T")),
        id("U")
    ),
    "(S ∖ T) ∖ U";
    "difference_left_child_parens"
)]
// prj1∼, not (prj1)∼: a bare relational atom (an atomic builtin per a8bbd8d)
// is a primary expression, so postfix inverse needs no parens. It would
// round-trip either way, but the canonical form must match the minimal one.
#[test_case(
    un(
        UnaryOp::Inverse,
        ExpressionKind::AtomicBuiltin(AtomicBuiltinKind::Prj1).into()
    ),
    "prj1\u{223C}";
    "inverse_of_atomic_builtin_no_parens"
)]
fn test_pretty_print_canonical_expression(expr: Expression, expected: &str) {
    let printed = PrettyPrinter::new().print_expression(&expr);
    assert_eq!(printed, expected);
    assert_eq!(
        parse_expression_str(&printed).expect("canonical form reparses"),
        expr,
        "reparsing the canonical form changed the AST"
    );
}

// (a > 0 ∧ b > 0) ∨ c > 0 — And inside Or keeps parens (different Camille
// compatibility classes).
#[test_case(
    logic(LogicalOp::Or, logic(LogicalOp::And, gt0("a"), gt0("b")), gt0("c")),
    "(a > 0 ∧ b > 0) ∨ c > 0";
    "and_or_left_child"
)]
// a > 0 ∧ (b > 0 ∨ c > 0) — Or inside And keeps parens.
#[test_case(
    logic(LogicalOp::And, gt0("a"), logic(LogicalOp::Or, gt0("b"), gt0("c"))),
    "a > 0 ∧ (b > 0 ∨ c > 0)";
    "or_inside_and"
)]
// a > 0 ∧ b > 0 ∧ c > 0 — same class, left-assoc: left child prints flat,
// only a right child would need parens.
#[test_case(
    logic(LogicalOp::And, logic(LogicalOp::And, gt0("a"), gt0("b")), gt0("c")),
    "a > 0 ∧ b > 0 ∧ c > 0";
    "and_chain_same_class"
)]
fn test_pretty_print_canonical_predicate(pred: Predicate, expected: &str) {
    let printed = PrettyPrinter::new().print_predicate(&pred);
    assert_eq!(printed, expected);
    assert_eq!(
        parse_predicate_str(&printed).expect("canonical form reparses"),
        pred,
        "reparsing the canonical form changed the AST"
    );
}

#[test]
fn test_pretty_print_function_application_binary_function_keeps_parens() {
    // (mapping ◁ prj1)(x): the function side is a Binary, so
    // dropping the parens would re-bind as `mapping ◁ prj1(x)`,
    // a different AST. Regression seen on a real-world corpus model.
    use rossi::ast::expression::{AtomicBuiltinKind, BinaryOp};
    let expr: Expression = ExpressionKind::FunctionApplication {
        function: Box::new(
            ExpressionKind::Binary {
                op: BinaryOp::DomainRestriction,
                left: Box::new(ExpressionKind::Identifier("mapping".into()).into()),
                right: Box::new(ExpressionKind::AtomicBuiltin(AtomicBuiltinKind::Prj1).into()),
            }
            .into(),
        ),
        argument: Box::new(ExpressionKind::Identifier("x".into()).into()),
    }
    .into();
    let output = PrettyPrinter::new().print_expression(&expr);
    assert_eq!(output, "(mapping \u{25C1} prj1)(x)");
}

#[test]
fn test_pretty_print_function_application_identifier_function_no_parens() {
    // f(x): the function side is an Identifier, so no parens needed.
    let expr: Expression = ExpressionKind::FunctionApplication {
        function: Box::new(ExpressionKind::Identifier("f".into()).into()),
        argument: Box::new(ExpressionKind::Identifier("x".into()).into()),
    }
    .into();
    let output = PrettyPrinter::new().print_expression(&expr);
    assert_eq!(output, "f(x)");
}

#[test]
fn test_single_argument_application_ast_roundtrips() {
    use rossi::ast::expression::BuiltinFunction;

    let applications: [(Expression, &str); 2] = [
        (
            ExpressionKind::FunctionApplication {
                function: Box::new(Expression::identifier("f")),
                argument: Box::new(Expression::identifier("x")),
            }
            .into(),
            "f(x)",
        ),
        (
            ExpressionKind::BuiltinApplication {
                function: BuiltinFunction::Card,
                argument: Box::new(Expression::identifier("x")),
            }
            .into(),
            "card(x)",
        ),
    ];

    for (application, expected) in applications {
        let printed = PrettyPrinter::new().print_expression(&application);
        assert_eq!(printed, expected);
        assert_eq!(rossi::parse_expression_str(&printed).unwrap(), application);
    }
}

// ============================================================================
// Camille compatibility class tests (parenthesization)
// ============================================================================

#[test]
fn test_camille_mixed_and_or_roundtrip() {
    // Roundtrip: (a ∧ b) ∨ c ∨ d ∨ (e ∧ f)
    let source = r#"CONTEXT test
AXIOMS
    @axm1 (a > 0 ∧ b > 0) ∨ c > 0 ∨ d > 0 ∨ (e > 0 ∧ f > 0)
END
"#;
    common::assert_roundtrip(source);
}

// ============================================================================
// Special roundtrip tests (individual — custom logic, not assert_roundtrip)
// ============================================================================

#[test]
fn test_roundtrip_maplet_comma_comma() {
    // `,,` is an accepted alternative input spelling for the maplet ↦; it
    // round-trips to the canonical ↦, so verify that glyph appears and that
    // the output parses back.
    let source = r#"
MACHINE test
VARIABLES
    r x y
INVARIANTS
    @inv1 r = x ,, y
END
"#;
    let component = parse(source).unwrap();
    let output = to_string(&component);
    assert!(
        output.contains('\u{21A6}'),
        "expected canonical maplet ↦ in output, got:\n{output}"
    );
    let _component2 = parse(&output).unwrap();
}

// ============================================================================
// Roundtrip feature tests (parametrized)
// ============================================================================

// Kept as a readable pinned example of machine-level REFINES with event-level
// REFINES/WITH; generative cover: machine_roundtrip_* in proptest_roundtrip.rs.
#[test_case(r#"MACHINE test
REFINES
    abs
VARIABLES
    x
EVENTS
    EVENT INITIALISATION
    THEN
        x := 0
    END

    EVENT update
    REFINES
        abs_update
    WHERE
        @grd1 x < 100
    WITH
        @abs_x abs_x = x
    THEN
        x := x + 1
    END
END
"# ; "with_clause")]
#[test_case("CONTEXT test\nAXIOMS\n    \u{2200}x\u{2982}\u{2124}\u{00B7}x > 0\nEND\n" ; "typed_forall")]
fn test_roundtrip_feature(source: &str) {
    common::assert_roundtrip(source);
}

// ============================================================================
// ASCII roundtrip tests (parametrized)
// ============================================================================

// Oftype
#[test_case("MACHINE test\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x \u{2208} \u{2115} \u{2982} \u{2124}\nEND\n" ; "oftype")]
// Typed identifiers in quantifiers
#[test_case("CONTEXT test\nAXIOMS\n    \u{2200}x\u{2982}\u{2124}\u{00B7}x > 0\nEND\n" ; "typed_forall")]
fn test_roundtrip_ascii(source: &str) {
    common::assert_roundtrip_ascii(source);
}

#[test]
fn test_set_comprehension_basic_unicode_bar() {
    let source = "MACHINE M\nEVENTS\n    EVENT e\n    THEN\n        @act1 v ≔ {x ∣ x ∈ S ∧ x ≠ 0}\n    END\nEND\n";
    let component = parse(source).unwrap();
    let output = to_string(&component);
    assert!(
        output.contains("∣"),
        "Basic set comprehension should use Unicode ∣, got: {}",
        output
    );
    assert!(
        !output.contains('|'),
        "Basic set comprehension should not contain ASCII |, got: {}",
        output
    );
}

#[test]
fn private_use_glyphs_flag_controls_relation_and_override_spelling() {
    let pred = parse_predicate_str("r ∈ A <<-> B ∧ s = f <+ g").expect("parses");

    // Default printer is portable: the private-use operators emit ASCII.
    let portable = PrettyPrinter::new().print_predicate(&pred);
    assert!(
        portable.contains("<<->") && portable.contains("<+"),
        "default printer should emit ASCII for private-use operators, got: {portable}"
    );
    assert!(
        !portable.contains('\u{E100}') && !portable.contains('\u{E103}'),
        "default printer must not emit a private-use glyph, got: {portable}"
    );

    // Opting in reproduces Rodin's internal spelling (the raw glyphs).
    let glyphs = PrettyPrinter::new()
        .with_private_use_glyphs(true)
        .print_predicate(&pred);
    assert!(
        glyphs.contains('\u{E100}') && glyphs.contains('\u{E103}'),
        "with_private_use_glyphs(true) should emit the glyphs, got: {glyphs}"
    );
}

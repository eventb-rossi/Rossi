//! Shared test utilities for Event-B parser integration tests.

#![allow(dead_code)]

use rossi::{
    Component, Context, Expression, Machine, PredicateKind, PrettyPrinter, format_str, parse,
    to_string, to_string_ascii,
};

/// Build an in-memory zip archive from `(entry name, content)` pairs.
pub fn zip_with_entries(entries: &[(&str, &[u8])]) -> Vec<u8> {
    let mut bytes = Vec::new();
    {
        let mut writer = zip::ZipWriter::new(std::io::Cursor::new(&mut bytes));
        let options = zip::write::SimpleFileOptions::default()
            .compression_method(zip::CompressionMethod::Stored);
        for (name, content) in entries {
            writer.start_file(*name, options).unwrap();
            std::io::Write::write_all(&mut writer, content).unwrap();
        }
        writer.finish().unwrap();
    }
    bytes
}

/// Clear all spans from a Component for AST comparison (spans differ after roundtrip).
pub fn clear_spans(component: &mut Component) {
    component.clear_spans();
}

/// Roundtrip helper: parse -> pretty-print -> re-parse -> compare ASTs.
pub fn assert_roundtrip(source: &str) {
    let mut component1 = parse(source).unwrap_or_else(|e| panic!("Failed to parse source: {e}"));
    let output = to_string(&component1);
    let mut component2 = parse(&output)
        .unwrap_or_else(|e| panic!("Failed to parse roundtrip output: {e}\nOutput was:\n{output}"));

    clear_spans(&mut component1);
    clear_spans(&mut component2);

    assert_eq!(
        component1, component2,
        "Roundtrip mismatch.\nOriginal source:\n{source}\nPretty-printed:\n{output}"
    );
}

/// Roundtrip helper for ASCII mode: parse -> ASCII print -> re-parse -> compare ASTs.
pub fn assert_roundtrip_ascii(source: &str) {
    let mut component1 = parse(source).unwrap_or_else(|e| panic!("Failed to parse source: {e}"));
    let output = to_string_ascii(&component1);
    let mut component2 = parse(&output).unwrap_or_else(|e| {
        panic!("Failed to parse ASCII roundtrip output: {e}\nOutput was:\n{output}")
    });

    clear_spans(&mut component1);
    clear_spans(&mut component2);

    assert_eq!(
        component1, component2,
        "ASCII roundtrip mismatch.\nOriginal source:\n{source}\nASCII output:\n{output}"
    );
}

/// Parse source and extract the Context, panicking if it's not a Context.
pub fn parse_context(source: &str) -> Context {
    match parse(source).unwrap_or_else(|e| panic!("Failed to parse: {e}")) {
        Component::Context(ctx) => ctx,
        Component::Machine(_) => panic!("Expected Context, got Machine"),
    }
}

/// Parse source and extract the Machine, panicking if it's not a Machine.
pub fn parse_machine(source: &str) -> Machine {
    match parse(source).unwrap_or_else(|e| panic!("Failed to parse: {e}")) {
        Component::Machine(m) => m,
        Component::Context(_) => panic!("Expected Machine, got Context"),
    }
}

/// Parse a Context source and return the RHS expression of the first axiom's comparison.
pub fn parse_axiom_rhs(source: &str) -> Expression {
    let ctx = parse_context(source);
    if let PredicateKind::Relational { right, .. } = ctx.axioms[0].predicate.kind() {
        return right.clone();
    }
    panic!("Expected Context with comparison axiom");
}

/// Format with `printer`, asserting output hygiene (no trailing
/// whitespace, exactly one final newline), the width limit on every
/// comment-free line when the printer wraps, and that the output reparses
/// to the same AST.
pub fn format_checked(source: &str, printer: &PrettyPrinter) -> String {
    let output = format_str(source, printer)
        .unwrap_or_else(|e| panic!("failed to format: {e}\nsource:\n{source}"));
    for line in output.lines() {
        assert_eq!(
            line.trim_end(),
            line,
            "trailing whitespace in output line {line:?}\noutput:\n{output}"
        );
    }
    assert!(
        output.ends_with('\n') && !output.ends_with("\n\n"),
        "output must end with exactly one newline, got:\n{output:?}"
    );
    if printer.max_line_width > 0 {
        // Comment text is never wrapped, so only comment-free lines are
        // held to the width.
        let masked = rossi::comments::lexical_spans(&output).mask_comments_chars(&output);
        for (line, masked_line) in output.lines().zip(masked.lines()) {
            if masked_line == line {
                assert!(
                    line.chars().count() <= printer.max_line_width,
                    "line exceeds width {}: {line:?}\noutput:\n{output}",
                    printer.max_line_width
                );
            }
        }
    }
    assert_reparses_equal(source, &output);
    output
}

/// Assert `output` reparses to the same AST as `source` (spans cleared).
pub fn assert_reparses_equal(source: &str, output: &str) {
    let mut original = parse(source).unwrap();
    let mut reparsed =
        parse(output).unwrap_or_else(|e| panic!("output does not reparse: {e}\noutput:\n{output}"));
    clear_spans(&mut original);
    clear_spans(&mut reparsed);
    assert_eq!(
        original, reparsed,
        "reparse mismatch\nsource:\n{source}\noutput:\n{output}"
    );
}

/// Parse a Context source and return the LHS expression of the first axiom's comparison.
pub fn parse_expr_axiom(source: &str) -> Expression {
    let ctx = parse_context(source);
    if let PredicateKind::Relational { left, .. } = ctx.axioms[0].predicate.kind() {
        return left.clone();
    }
    panic!("Expected Context with comparison axiom");
}

/// Generate a CONTEXT source with given constants and axiom body.
///
/// Example: `axiom_context("x, y, r", "r = x |-> y")` produces:
/// ```text
/// CONTEXT test
/// CONSTANTS
///     x, y, r
/// AXIOMS
///     @axm1 r = x |-> y
/// END
/// ```
pub fn axiom_context(constants: &str, axiom_body: &str) -> String {
    let constants = ws_idents(constants);
    format!("CONTEXT test\nCONSTANTS\n    {constants}\nAXIOMS\n    @axm1 {axiom_body}\nEND\n")
}

/// Generate a MACHINE source with given variables and invariant body.
pub fn invariant_machine(variables: &str, invariant_body: &str) -> String {
    let variables = ws_idents(variables);
    format!(
        "MACHINE test\nVARIABLES\n    {variables}\nINVARIANTS\n    @inv1 {invariant_body}\nEND\n"
    )
}

/// Declared identifiers are whitespace-separated. Accept either spelling from a
/// caller and normalise to whitespace so the generated fixture parses (a comma
/// between declared names is a parse error in the real grammar).
fn ws_idents(idents: &str) -> String {
    idents
        .split(|c: char| c == ',' || c.is_whitespace())
        .filter(|s| !s.is_empty())
        .collect::<Vec<_>>()
        .join(" ")
}

//! The stdin channel (`-`, `--stdin-filename`, closed pipes) and the parser
//! nesting-depth limit exercised through the full CLI pipeline.

use rossi::MAX_NESTING_DEPTH;

use crate::helpers::{ASCII_CONTEXT, rossi_command, run_cli_with_stdin};

/// A context whose single axiom nests parentheses `n` deep.
fn nested_paren_context(n: usize) -> String {
    format!(
        "context C axioms @a {}x{} = 1 end",
        "(".repeat(n),
        ")".repeat(n)
    )
}

#[test]
fn validate_stdin_at_nesting_limit_succeeds() {
    // Runs the full validate pipeline in a debug build — proves the parser
    // stack headroom covers the depth limit end to end.
    let output = run_cli_with_stdin(&["validate", "-"], &nested_paren_context(MAX_NESTING_DEPTH));
    assert!(
        output.status.success(),
        "validate - at the nesting limit should exit 0; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn validate_stdin_over_nesting_limit_reports_error_not_crash() {
    // Used to die with SIGABRT ("has overflowed its stack"); must now exit
    // with an ordinary diagnostic.
    let output = run_cli_with_stdin(&["validate", "-"], &nested_paren_context(5000));
    assert!(
        output.status.code().is_some(),
        "validate - must not be killed by a signal"
    );
    assert!(!output.status.success());
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        combined.contains("nesting exceeds the maximum depth"),
        "expected a NestingTooDeep diagnostic, got: {combined}"
    );
}

#[test]
fn fmt_stdin_at_nesting_limit_succeeds() {
    let output = run_cli_with_stdin(&["fmt", "-"], &nested_paren_context(MAX_NESTING_DEPTH));
    assert!(
        output.status.success(),
        "fmt - at the nesting limit should exit 0; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn validate_stdin_at_limit_negation_chain_succeeds() {
    // Unlike parens (which collapse in the AST), a negation chain stays
    // nested all the way through the static checks — this exercises the
    // downstream consumers at depth in a debug build.
    let source = format!(
        "context C axioms @a {}(1=1) end",
        "¬".repeat(MAX_NESTING_DEPTH - 1)
    );
    let output = run_cli_with_stdin(&["validate", "-"], &source);
    assert!(
        output.status.code().is_some(),
        "validate - must not be killed by a signal"
    );
    assert!(
        output.status.success(),
        "validate - at-limit negation chain should exit 0; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Run structured validation after closing the read end of its stdout pipe.
fn run_validate_with_closed_stdout(format: &str, stdin_data: &str) -> std::process::Output {
    use std::io::Write;
    use std::process::Stdio;

    let mut child = rossi_command()
        .args(["validate", "--format", format, "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Failed to spawn rossi-cli");
    drop(child.stdout.take());
    child
        .stdin
        .take()
        .expect("child stdin")
        .write_all(stdin_data.as_bytes())
        .expect("write stdin");
    child.wait_with_output().expect("wait for rossi-cli")
}

#[test]
fn validate_structured_output_handles_broken_pipe_without_panicking() {
    for format in ["json", "sarif"] {
        let output = run_validate_with_closed_stdout(format, ASCII_CONTEXT);
        assert!(
            output.status.success(),
            "valid {format} validation should ignore BrokenPipe; stderr={}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            !String::from_utf8_lossy(&output.stderr).contains("panicked"),
            "{format} output must not panic on BrokenPipe"
        );

        let output = run_validate_with_closed_stdout(format, "CONTEXT");
        assert!(
            !output.status.success(),
            "BrokenPipe must preserve failed {format} validation status"
        );
        assert!(
            !String::from_utf8_lossy(&output.stderr).contains("panicked"),
            "failed {format} validation must not panic on BrokenPipe"
        );
    }
}

#[test]
fn validate_stdin_uses_stdin_filename() {
    let output = run_cli_with_stdin(
        &[
            "validate",
            "--format",
            "json",
            "--stdin-filename",
            "foo.eventb",
            "-",
        ],
        ASCII_CONTEXT,
    );
    assert!(
        output.status.success(),
        "validate - should exit 0; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("\"file\": \"foo.eventb\""),
        "expected the stdin filename in JSON: {stdout}"
    );
    assert!(
        stdout.contains("\"success\": true"),
        "expected a successful parse: {stdout}"
    );
}

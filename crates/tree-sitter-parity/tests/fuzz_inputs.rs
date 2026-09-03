//! Both-direction parity between Rossi's parser and the tree-sitter grammar,
//! over a directory of inputs produced by the fuzzer.
//!
//! `corpus.rs` checks one direction over real models: everything Rossi accepts,
//! tree-sitter must accept too. Fuzz inputs are the other half of the picture —
//! they are generated *from* the tree-sitter grammar, so they also show where
//! tree-sitter accepts text Rossi refuses, which is where the two grammars
//! disagree about the language.
//!
//! This test reports; it does not gate. Point it at an input directory:
//!
//!   EVENTB_FUZZ_INPUTS=<dir> \
//!     cargo test --manifest-path crates/tree-sitter-parity/Cargo.toml \
//!     --test fuzz_inputs -- --nocapture
//!
//! With the variable unset it prints a SKIP line and passes. That is a weaker
//! rule than the fuzzer applies to the grammar itself, whose absence fails
//! under CI — deliberately, because these inputs are produced by a run rather
//! than checked in, so there is nothing for CI to find.

mod common;

/// Above this many inputs, only the disagreements are listed.
const PER_INPUT_LIMIT: usize = 200;

/// How Rossi answered, with a crash as a verdict of its own.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Verdict {
    Accept,
    Reject,
    Crash,
}

impl Verdict {
    fn label(self) -> &'static str {
        match self {
            Verdict::Accept => "accept",
            Verdict::Reject => "REJECT",
            Verdict::Crash => "CRASH",
        }
    }
}

fn rossi_verdict(text: &str) -> Verdict {
    match common::without_panicking(|| rossi::parse_components(text).is_ok()) {
        Some(true) => Verdict::Accept,
        Some(false) => Verdict::Reject,
        None => Verdict::Crash,
    }
}

#[test]
fn report_parity_over_fuzz_inputs() {
    let Some(directory) = common::directory_from_env("EVENTB_FUZZ_INPUTS") else {
        eprintln!("SKIP fuzz_inputs: no input directory (set EVENTB_FUZZ_INPUTS)");
        return;
    };
    let inputs = common::collect_files(&directory, "eventb").expect("read the input directory");
    assert!(
        !inputs.is_empty(),
        "input directory holds no .eventb files: {}",
        directory.display()
    );

    let mut parser = common::eventb_parser();
    let mut both = 0usize;
    let mut neither = 0usize;
    let mut rossi_only = Vec::new();
    let mut tree_sitter_only = Vec::new();
    let mut crashed = Vec::new();

    for input in &inputs {
        let text = std::fs::read_to_string(input).expect("read input");
        let rossi = rossi_verdict(&text);
        let tree_sitter = common::tree_sitter_accepts(&mut parser, &text);
        match (rossi, tree_sitter) {
            (Verdict::Accept, true) => both += 1,
            (Verdict::Reject, false) => neither += 1,
            (Verdict::Accept, false) => rossi_only.push(input.clone()),
            (Verdict::Reject, true) => tree_sitter_only.push(input.clone()),
            (Verdict::Crash, _) => crashed.push(input.clone()),
        }
        // A per-input line is what makes a small, hand-built set of probe
        // cases readable; a fuzzing run's directory is far too large for it.
        if inputs.len() <= PER_INPUT_LIMIT {
            let name = input.file_stem().unwrap_or_default().to_string_lossy();
            println!(
                "  {name:<34} rossi={:<7} tree-sitter={}",
                rossi.label(),
                if tree_sitter { "accept" } else { "REJECT" }
            );
        }
    }

    println!(
        "parity over {} inputs: {both} accepted by both, {neither} by neither, \
         {} only by rossi, {} only by tree-sitter, {} crashed rossi",
        inputs.len(),
        rossi_only.len(),
        tree_sitter_only.len(),
        crashed.len()
    );
    for (label, group) in [
        ("ROSSI-ONLY      ", &rossi_only),
        ("TREE-SITTER-ONLY", &tree_sitter_only),
        ("CRASHED-ROSSI   ", &crashed),
    ] {
        for input in group.iter().take(20) {
            println!("  {label} {}", input.display());
        }
    }
}

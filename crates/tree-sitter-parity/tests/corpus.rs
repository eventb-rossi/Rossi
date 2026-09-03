//! Corpus parity gate for the standalone tree-sitter grammar.
//!
//! Every component recovered from the external Rodin corpus is rendered in
//! Unicode and ASCII. A rendering enters the parity set only when Rossi's
//! strict parser accepts it; tree-sitter must then produce no `ERROR` or
//! `MISSING` nodes.
//!
//! This crate sits outside the workspace (its `tree-sitter-eventb` dependency
//! is a path into the grammar submodule), so a plain `cargo test` never reaches
//! it. Point `EVENTB_CORPUS_DIR` at a corpus checkout and run it explicitly:
//!
//!   EVENTB_CORPUS_DIR=<corpus> \
//!     cargo test --manifest-path crates/tree-sitter-parity/Cargo.toml -- --nocapture
//!
//! With the variable unset the test prints a SKIP line and passes.

mod common;

use common::first_issue;

#[test]
fn tree_sitter_accepts_every_rossi_valid_rendering() {
    let Some(corpus) = common::directory_from_env("EVENTB_CORPUS_DIR") else {
        eprintln!("SKIP tree_sitter_corpus: no corpus (set EVENTB_CORPUS_DIR)");
        return;
    };
    let archives = common::collect_files(&corpus, "zip").expect("read corpus directory");
    assert!(
        !archives.is_empty(),
        "selected corpus contains no .zip archives"
    );

    let mut parser = common::eventb_parser();
    let unicode = rossi::PrettyPrinter::new();
    let ascii = rossi::PrettyPrinter::ascii();

    let mut imported = 0usize;
    let mut checked = 0usize;
    let mut excluded = 0usize;
    let mut failures = Vec::<String>::new();

    for (archive_index, archive) in archives.into_iter().enumerate() {
        let bytes = std::fs::read(&archive).expect("read corpus archive");
        let result = rossi::parse_zip_with_recovery(&bytes);
        excluded += result.errors.len();

        for (component_index, named) in result.component.unwrap_or_default().into_iter().enumerate()
        {
            imported += 1;
            for (rendering, printer) in [("unicode", &unicode), ("ascii", &ascii)] {
                let Some(text) =
                    common::without_panicking(|| printer.print_component(&named.component))
                else {
                    excluded += 1;
                    continue;
                };

                if rossi::parse(&text).is_err() {
                    excluded += 1;
                    continue;
                }

                checked += 1;
                let tree = parser
                    .parse(&text, None)
                    .expect("tree-sitter parser was cancelled");
                if let Some(issue) = first_issue(tree.root_node()) {
                    failures.push(format!(
                        "archive #{}, component #{} ({rendering}): {} {}..{}",
                        archive_index + 1,
                        component_index + 1,
                        issue.kind(),
                        issue.start_position(),
                        issue.end_position()
                    ));
                }
            }
        }
    }

    println!(
        "tree-sitter corpus: {checked} Rossi-valid renderings from {imported} components, \
         {excluded} exclusions, {} failures",
        failures.len()
    );

    if !failures.is_empty() {
        for failure in &failures {
            eprintln!("  FAIL  {failure}");
        }
        panic!(
            "{} / {checked} Rossi-valid renderings failed tree-sitter parsing",
            failures.len()
        );
    }
}

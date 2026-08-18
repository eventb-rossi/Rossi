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

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};

use tree_sitter::{Node, Parser};

/// The repository root (two levels up from this crate's manifest).
fn repository_root() -> PathBuf {
    let mut p = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    p.pop();
    p.pop();
    p
}

/// The corpus directory named by `EVENTB_CORPUS_DIR`, or `None` when the
/// variable is unset or does not name a directory (skip-when-unset). A relative
/// value is resolved from the repository root, matching how the in-workspace
/// corpus harnesses read the same variable. There is no default location: the
/// corpus lives outside this repository and only the caller knows where.
fn corpus_dir() -> Option<PathBuf> {
    let path = PathBuf::from(std::env::var("EVENTB_CORPUS_DIR").ok()?);
    let path = if path.is_absolute() {
        path
    } else {
        repository_root().join(path)
    };
    path.is_dir().then_some(path)
}

/// The `.zip` corpus models in `dir`, sorted for deterministic iteration.
fn collect_zips(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut zips: Vec<PathBuf> = std::fs::read_dir(dir)?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "zip"))
        .collect();
    zips.sort();
    Ok(zips)
}

fn first_issue(node: Node<'_>) -> Option<Node<'_>> {
    if node.is_error() || node.is_missing() {
        return Some(node);
    }
    (0..node.child_count() as u32).find_map(|index| first_issue(node.child(index)?))
}

fn render_silently(printer: &rossi::PrettyPrinter, component: &rossi::Component) -> Option<String> {
    let previous_hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let rendered = catch_unwind(AssertUnwindSafe(|| printer.print_component(component))).ok();
    std::panic::set_hook(previous_hook);
    rendered
}

#[test]
fn tree_sitter_accepts_every_rossi_valid_rendering() {
    let Some(corpus) = corpus_dir() else {
        eprintln!("SKIP tree_sitter_corpus: no corpus (set EVENTB_CORPUS_DIR)");
        return;
    };
    let archives = collect_zips(&corpus).expect("read corpus directory");
    assert!(
        !archives.is_empty(),
        "selected corpus contains no .zip archives"
    );

    let mut parser = Parser::new();
    parser
        .set_language(&tree_sitter_eventb::LANGUAGE.into())
        .expect("load tree-sitter Event-B grammar");
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
                let Some(text) = render_silently(printer, &named.component) else {
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

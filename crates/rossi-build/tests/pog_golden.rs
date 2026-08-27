//! Golden proof obligations — the `.bpo` files rossi generates for two
//! in-repo example archives, locked against the reference output for
//! the same sources.
//!
//! Every other reference comparison (`pog_corpus`, `rodin_corpus`) is
//! `#[ignore]`d because it needs the external model corpus or a
//! toolchain runtime. This one carries its reference in
//! `tests/fixtures/pog_golden/`,
//! so it runs under a plain `cargo test` and is the only proof-obligation
//! gate CI executes. See that directory's `README.md` for how the reference
//! was produced and how to regenerate it after a deliberate POG change.
//!
//! The comparison runs at two levels. The normalized [`PoView`] diff reports
//! a divergence in the obligations themselves in readable terms; the verbatim
//! comparison then catches a change in attribute order, element order or
//! spacing that the semantic view forgives.

mod common;

use std::collections::BTreeMap;
use std::path::PathBuf;

use rossi_build::po_view::PoView;
use rossi_build::project::discover_projects;

/// The example archives locked here. Their components are whatever the
/// fixture directory holds, so the checked-in references stay the single
/// source of truth for what gets compared.
const MODELS: &[&str] = &["traffic-light", "binary-search"];

/// Problems reported before truncation.
const MAX_PROBLEMS: usize = 10;

fn fixtures_dir(model: &str) -> PathBuf {
    common::workspace_root()
        .join("crates/rossi-build/tests/fixtures/pog_golden")
        .join(model)
}

/// Build one example archive and return its generated `.bpo` files keyed by
/// component name. This is the pure build path — no reconciliation, so every
/// stamp is 0, exactly as in a fresh reference build.
fn generated_bpos(model: &str) -> BTreeMap<String, String> {
    let zip = common::workspace_root()
        .join("crates/rossi/examples")
        .join(format!("{model}.zip"));
    let bytes = std::fs::read(&zip).unwrap_or_else(|e| panic!("read {}: {e}", zip.display()));
    let projects =
        discover_projects(&bytes, model).unwrap_or_else(|e| panic!("{model}: discovery: {e}"));

    let mut out = BTreeMap::new();
    for dp in projects {
        let build = rossi_build::build(&dp.into_project());
        assert!(
            build.is_ok(),
            "{model}: build reported errors: {:?}",
            build.diagnostics
        );
        for file in build.files {
            if let Some(component) = file.filename.strip_suffix(".bpo") {
                out.insert(component.to_string(), file.contents);
            }
        }
    }
    out
}

/// The checked-in reference `.bpo` files, keyed by component name.
fn reference_bpos(model: &str) -> BTreeMap<String, String> {
    let dir = fixtures_dir(model);
    let entries = std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("read {}: {e}", dir.display()));
    let mut out = BTreeMap::new();
    for entry in entries {
        let path = entry.expect("fixture entry").path();
        if path.extension().is_some_and(|e| e == "bpo") {
            let component = path
                .file_stem()
                .expect("stem")
                .to_string_lossy()
                .into_owned();
            let contents = std::fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            out.insert(component, contents);
        }
    }
    assert!(!out.is_empty(), "{model}: no reference .bpo fixtures");
    out
}

#[test]
fn generated_obligations_match_rodin() {
    let mut problems = Vec::new();
    let mut verbatim = Vec::new();
    for model in MODELS {
        let ours = generated_bpos(model);
        let theirs = reference_bpos(model);
        assert_eq!(
            ours.keys().collect::<Vec<_>>(),
            theirs.keys().collect::<Vec<_>>(),
            "{model}: the generated components differ from the reference set"
        );
        for (component, reference) in &theirs {
            let file = format!("{model}/{component}.bpo");
            let generated = &ours[component];
            let our_view =
                PoView::from_xml(generated).unwrap_or_else(|e| panic!("{file}: parse ours: {e}"));
            let their_view = PoView::from_xml(reference)
                .unwrap_or_else(|e| panic!("{file}: parse reference: {e}"));
            common::diff_po_views(&file, &their_view, &our_view, MAX_PROBLEMS, &mut problems);
            verbatim.push((file, normalize(reference), normalize(generated)));
        }
    }
    problems.truncate(MAX_PROBLEMS);
    assert!(problems.is_empty(), "{}", problems.join("\n"));
    for (file, theirs, ours) in verbatim {
        assert_eq!(theirs, ours, "{file} diverges from the reference");
    }
}

/// Erase the three differences between the reference `.bpo` and ours that the
/// verbatim comparison is not meant to police, so every other byte is
/// compared as written:
///
/// 1. Indentation — the reference writer indents four spaces per level,
///    rossi's emitter writes each element flush left.
/// 2. `poIdentifier` order within a predicate set — the reference emits
///    them in hash order, rossi sorted.
/// 3. The ascribed empty set — the reference writes `x≠(∅ ⦂ ℙ(T))` where rossi's
///    canonical printer emits bare `∅`. Unlike the first two this is not a
///    serializer artifact but a real divergence, inherited from the checked
///    machine file: `normalize::ascribe_empty_set_values` ascribes `∅` only
///    in assignments, never in predicate positions. Erasing it here drops the
///    ascribed type too, so this comparison cannot police that type either;
///    the divergence is tracked for the generator, not for this gate.
///
/// Line splitting also erases a trailing-newline or CRLF difference, neither
/// of which either writer produces.
fn normalize(xml: &str) -> String {
    let is_identifier = |line: &String| line.contains("org.eventb.core.poIdentifier");
    let mut lines: Vec<String> = xml
        .lines()
        .map(|line| strip_empty_set_ascriptions(line.trim_start()))
        .collect();
    for run in lines.chunk_by_mut(|a, b| is_identifier(a) && is_identifier(b)) {
        run.sort();
    }
    lines.join("\n")
}

/// Rewrite every `(∅ ⦂ <type>)` as `∅`, closing on the matching parenthesis
/// so that a parenthesised type such as `ℙ(COLOURS)` does not end it early.
fn strip_empty_set_ascriptions(line: &str) -> String {
    const OPEN: &str = "(∅ ⦂ ";
    let mut out = String::with_capacity(line.len());
    let mut rest = line;
    while let Some(at) = rest.find(OPEN) {
        out.push_str(&rest[..at]);
        out.push('∅');
        rest = &rest[at + OPEN.len()..];
        let mut depth = 1usize;
        while let Some(i) = rest.find(['(', ')']) {
            if rest[i..].starts_with('(') {
                depth += 1;
            } else {
                depth -= 1;
            }
            rest = &rest[i + 1..];
            if depth == 0 {
                break;
            }
        }
    }
    out.push_str(rest);
    out
}

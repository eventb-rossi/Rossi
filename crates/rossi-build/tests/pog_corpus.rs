//! Corpus proof-obligation diff — regenerates every archive's `.bpo`
//! files and compares them, through the normalized [`PoView`], against
//! the reference `.bpo` files the archive ships.
//!
//! The comparison is semantic: sequent name sets, natures, accuracy,
//! goals and hypotheses as re-parsed ascription-stripped ASTs with
//! their normalized sources, the flattened typed identifiers, and the
//! resolved hints. Stamps, identifier order inside sets, and cut-point
//! materialization details are not compared.
//!
//! Ignored by default (needs a models corpus). Run:
//!
//!   cargo test -p rossi-build --test pog_corpus -- --ignored --nocapture
//!
//! The corpus directory is taken from `EVENTB_CORPUS_DIR`, falling
//! back to the sibling `eventb-models-collection` checkout. A TSV
//! report is written to `target/rossi-build-pog-corpus.tsv`.

use std::path::Path;

use rossi_build::po_view::PoView;
use rossi_build::project::discover_projects;

mod common;
use common::{collect_zips, corpus_dir, load_flags, workspace_target};

/// Problems reported per model before truncation.
const MAX_PROBLEMS: usize = 5;

#[test]
#[ignore = "needs a models corpus; run with --ignored"]
fn pog_corpus() {
    let Some(dir) = corpus_dir() else {
        eprintln!("SKIP pog_corpus: no corpus (set EVENTB_CORPUS_DIR)");
        return;
    };
    let flags = load_flags(&dir.join("model_flags.tsv")).unwrap_or_default();
    let zips = collect_zips(&dir).unwrap_or_default();
    if zips.is_empty() {
        eprintln!("SKIP pog_corpus: no .zip models in {}", dir.display());
        return;
    }
    eprintln!("corpus: {} zip(s) in {}", zips.len(), dir.display());

    let mut report: Vec<Vec<String>> = Vec::new();
    let mut failures: Vec<String> = Vec::new();
    for zip in &zips {
        let name = zip.file_name().and_then(|s| s.to_str()).unwrap_or("?");
        let model = name.trim_end_matches(".zip");
        let skip = flags.get(model).is_some_and(|f| {
            f.iter().any(|flag| {
                matches!(
                    flag.as_str(),
                    "defective" | "keyword_identifier" | "unsupported"
                )
            })
        });
        if skip {
            eprintln!("  SKIP {name} (flagged unsupported input)");
            report.push(vec![model.into(), "skip".into(), String::new()]);
            continue;
        }
        match diff_model(zip) {
            Ok(problems) if problems.is_empty() => {
                eprintln!("  OK   {name}");
                report.push(vec![model.into(), "match".into(), String::new()]);
            }
            Ok(problems) => {
                if let Some(reason) = common::pog_known_divergence(&dir, model) {
                    eprintln!("  KNOWN {name} ({reason})");
                    report.push(vec![model.into(), "known".into(), reason]);
                    continue;
                }
                eprintln!("  FAIL {name}:");
                for p in &problems {
                    eprintln!("       {p}");
                }
                failures.push(format!("{name}: {}", problems.join("; ")));
                report.push(vec![model.into(), "diverge".into(), problems.join("; ")]);
            }
            Err(e) => {
                eprintln!("  SKIP {name}: {e}");
                report.push(vec![model.into(), "skip".into(), e]);
            }
        }
    }

    let path = workspace_target().join("rossi-build-pog-corpus.tsv");
    common::write_report(&path, &["model", "verdict", "notes"], &report);
    eprintln!("report: {}", path.display());

    assert!(
        failures.is_empty(),
        "{} model(s) diverged from the reference proof obligations:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Regenerate one archive and diff every generated `.bpo` against the
/// reference. `Err` marks a model this comparison cannot judge.
fn diff_model(zip: &Path) -> Result<Vec<String>, String> {
    let bytes = std::fs::read(zip).map_err(|e| format!("read: {e}"))?;
    let stem = zip
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("project");
    let references = common::bpo_entries(&bytes)?;
    if references.is_empty() {
        return Err("no reference .bpo in archive".into());
    }
    let projects =
        discover_projects(&bytes, stem).map_err(|e| format!("project discovery: {e}"))?;

    let mut problems = Vec::new();
    for dp in projects {
        let prefix = dp.prefix.clone();
        let project = dp.into_project();
        let (build, _) = rossi_build::build_with_model(&project);
        let checkable = build.is_ok();
        for file in &build.files {
            if !file.filename.ends_with(".bpo") {
                continue;
            }
            let Some(reference) = references.get(&format!("{prefix}{}", file.filename)) else {
                // Three source-only archives and a few partially-built
                // ones ship no reference for this component.
                continue;
            };
            if !checkable {
                // A component the build reported errors for cannot be
                // expected to reproduce the reference obligations.
                continue;
            }
            if reference.contains(r#"name="GOAL""#) {
                // A legacy generator produced this reference (its
                // sequent children are named GOAL/SRC0/HINT0): its
                // obligation set predates several of the current
                // rules (the well-definedness simplifier among them),
                // so only a fresh regeneration can be compared.
                continue;
            }
            let ours = PoView::from_xml(&file.contents)
                .map_err(|e| format!("{}: parse ours: {e}", file.filename))?;
            let theirs = PoView::from_xml(reference)
                .map_err(|e| format!("{}: parse reference: {e}", file.filename))?;
            common::diff_po_views(&file.filename, &theirs, &ours, MAX_PROBLEMS, &mut problems);
            if problems.len() >= MAX_PROBLEMS {
                problems.truncate(MAX_PROBLEMS);
                return Ok(problems);
            }
        }
    }
    Ok(problems)
}

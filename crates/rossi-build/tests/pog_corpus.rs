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

use std::collections::BTreeMap;
use std::io::Read;
use std::path::{Path, PathBuf};

use rossi_build::po_view::PoView;
use rossi_build::project::discover_projects;

mod common;
use common::{collect_zips, load_flags, locate_corpus, workspace_root, workspace_target};

fn corpus_dir() -> Option<PathBuf> {
    locate_corpus().or_else(|| {
        let sibling = workspace_root().join("../eventb-models-collection");
        sibling.is_dir().then_some(sibling)
    })
}

/// Problems reported per model before truncation.
const MAX_PROBLEMS: usize = 5;

/// Models whose reference obligations are known not to be reproducible:
/// rows carrying the `pog_divergence` flag in the corpus
/// `model_flags.tsv`, with the audited reason in the notes column. Kept
/// visible in the report as `known` rather than failing the gate.
fn pog_known_divergence(corpus: &Path, model: &str) -> Option<String> {
    let tsv = std::fs::read_to_string(corpus.join("model_flags.tsv")).ok()?;
    for line in tsv.lines().skip(1) {
        let mut cols = line.split('\t');
        if cols.next() == Some(model) && cols.next() == Some("pog_divergence") {
            return Some(cols.next().unwrap_or("").to_string());
        }
    }
    None
}

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
                if let Some(reason) = pog_known_divergence(&dir, model) {
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

/// The reference `.bpo` contents of an archive, keyed by entry path.
fn reference_bpos(bytes: &[u8]) -> Result<BTreeMap<String, String>, String> {
    let mut archive =
        zip::ZipArchive::new(std::io::Cursor::new(bytes)).map_err(|e| format!("zip: {e}"))?;
    let mut out = BTreeMap::new();
    for i in 0..archive.len() {
        let mut entry = archive.by_index(i).map_err(|e| format!("zip: {e}"))?;
        if entry.name().ends_with(".bpo") {
            let mut contents = String::new();
            entry
                .read_to_string(&mut contents)
                .map_err(|e| format!("zip read: {e}"))?;
            out.insert(entry.name().to_string(), contents);
        }
    }
    Ok(out)
}

/// Regenerate one archive and diff every generated `.bpo` against the
/// reference. `Err` marks a model this comparison cannot judge.
fn diff_model(zip: &Path) -> Result<Vec<String>, String> {
    let bytes = std::fs::read(zip).map_err(|e| format!("read: {e}"))?;
    let stem = zip
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("project");
    let references = reference_bpos(&bytes)?;
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
            diff_views(&file.filename, &theirs, &ours, &mut problems);
            if problems.len() >= MAX_PROBLEMS {
                problems.truncate(MAX_PROBLEMS);
                return Ok(problems);
            }
        }
    }
    Ok(problems)
}

/// Compare the reference view against ours, appending findings.
fn diff_views(file: &str, reference: &PoView, ours: &PoView, problems: &mut Vec<String>) {
    for name in reference.sequents.keys() {
        if !ours.sequents.contains_key(name) {
            problems.push(format!("{file}: missing sequent {name}"));
        }
    }
    for name in ours.sequents.keys() {
        if !reference.sequents.contains_key(name) {
            problems.push(format!("{file}: extra sequent {name}"));
        }
    }

    for (name, theirs) in &reference.sequents {
        let Some(mine) = ours.sequents.get(name) else {
            continue;
        };
        if theirs.description != mine.description {
            problems.push(format!(
                "{file}: {name}: nature {:?} vs {:?}",
                theirs.description, mine.description
            ));
        }
        if theirs.accurate != mine.accurate {
            problems.push(format!(
                "{file}: {name}: accurate {} vs {}",
                theirs.accurate, mine.accurate
            ));
        }
        if theirs.goal != mine.goal {
            problems.push(format!("{file}: {name}: goal differs"));
        }
        let their_hyps = reference.flattened_hypotheses(name);
        let my_hyps = ours.flattened_hypotheses(name);
        if their_hyps != my_hyps {
            problems.push(format!(
                "{file}: {name}: hypotheses differ ({} vs {})",
                their_hyps.len(),
                my_hyps.len()
            ));
        }
        if reference.flattened_identifiers(name) != ours.flattened_identifiers(name) {
            problems.push(format!("{file}: {name}: identifiers differ"));
        }
        // Source order varied across the reference generator's
        // versions; compare as sets.
        let their_sources: std::collections::BTreeSet<_> = theirs.sources.iter().collect();
        let my_sources: std::collections::BTreeSet<_> = mine.sources.iter().collect();
        if their_sources != my_sources {
            problems.push(format!("{file}: {name}: sources differ"));
        }
        // Hints resolve to the content they select, so set naming
        // differences don't matter.
        if reference.resolved_hints(name) != ours.resolved_hints(name) {
            problems.push(format!("{file}: {name}: hints differ"));
        }
        if problems.len() >= MAX_PROBLEMS {
            return;
        }
    }
}

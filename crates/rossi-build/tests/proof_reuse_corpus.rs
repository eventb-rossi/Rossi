//! Corpus gate: dependency-based proof reuse against recorded statuses.
//!
//! For every obligation of every pristine archive, build the prover
//! sequent from the `.bpo`, read the stored proof's dependencies from
//! the `.bpr`, and compare the status-update verdict with the recorded
//! `.bps` row. Only rows whose stamp still matches their obligation
//! are comparable — a row is recomputed exactly when the stamp
//! changed, so a stale row records a verdict about a sequent that no
//! longer exists. Legacy vintages, unsupported proofs, and proofs
//! distrusted purely by reasoner-version drift are measured classes,
//! never divergences: the recorded verdict predates today's registry.
//!
//! Run with `--ignored`; the report lands in
//! `target/rossi-build-proof-reuse-corpus.tsv`.

mod common;

use std::collections::BTreeMap;
use std::io::{BufReader, Read};
use std::path::Path;

use common::{
    collect_zips, corpus_dir, flagged_unsupported, load_flags, prove_known_divergence,
    workspace_root, write_report,
};
use rossi_prove::bpr::{self, Keep, ProofBody, ProofEntry};
use rossi_prove::bps::{PsStatus, read_bps};
use rossi_prove::confidence::Confidence;
use rossi_prove::po_loader::{PoFile, PoProject};
use rossi_prove::status::compute_status;
use rossi_prove::tree::ProofTreeNode;

#[derive(Default)]
struct Counts {
    pos: usize,
    matched: usize,
    broken_match: usize,
    unattempted: usize,
    stale: usize,
    context_dep: usize,
    version_conflict: usize,
    unsupported: usize,
    legacy: usize,
    load_error: usize,
    missing_proof: usize,
    broken_mismatch: usize,
    reuse_ok: usize,
    diverge: usize,
}

impl Counts {
    fn add(&mut self, other: &Counts) {
        self.pos += other.pos;
        self.matched += other.matched;
        self.broken_match += other.broken_match;
        self.unattempted += other.unattempted;
        self.stale += other.stale;
        self.context_dep += other.context_dep;
        self.version_conflict += other.version_conflict;
        self.unsupported += other.unsupported;
        self.legacy += other.legacy;
        self.load_error += other.load_error;
        self.missing_proof += other.missing_proof;
        self.broken_mismatch += other.broken_mismatch;
        self.reuse_ok += other.reuse_ok;
        self.diverge += other.diverge;
    }
}

/// Normalizes a recorded or computed confidence: anything at or below
/// unattempted reads as "no confidence".
fn norm(confidence: Option<i32>) -> Option<i32> {
    confidence.filter(|c| *c > Confidence::UNATTEMPTED.0)
}

fn check_component(
    project: &PoProject,
    component: &str,
    path: &str,
    bps: Option<&str>,
    bpr: Option<&[u8]>,
    counts: &mut Counts,
    problems: &mut Vec<String>,
) {
    let Some(po) = project.file(path) else {
        return;
    };
    let rows: BTreeMap<String, PsStatus> = match bps {
        Some(bps) => match read_bps(bps.as_bytes()) {
            Ok(rows) => rows
                .into_iter()
                .map(|row| (row.name.clone(), row))
                .collect(),
            Err(err) => {
                counts.load_error += 1;
                problems.push(format!("{component}: {err}"));
                return;
            }
        },
        None => BTreeMap::new(),
    };
    let proofs: BTreeMap<String, ProofEntry> = match bpr {
        Some(bytes) => match bpr::read_bpr(bytes, |_| Keep::Full) {
            Ok(entries) => entries
                .into_iter()
                .map(|entry| (entry.name.clone(), entry))
                .collect(),
            Err(bpr::BprError::Unsupported(_)) => {
                // A pre-versioning proof file: every obligation of the
                // component is out of scope.
                counts.legacy += po.sequents().count();
                counts.pos += po.sequents().count();
                return;
            }
            Err(err) => {
                counts.load_error += 1;
                problems.push(format!("{component}: {err}"));
                return;
            }
        },
        None => BTreeMap::new(),
    };

    for entry in po.sequents() {
        counts.pos += 1;
        let name = &entry.name;
        let row = rows.get(name);
        let recorded_broken = row.is_some_and(|row| row.broken);
        let recorded_conf = norm(row.and_then(|row| row.confidence));
        let stamp_valid = match row {
            Some(row) => row.po_stamp == entry.stamp,
            // No row at all reads as a fresh unattempted status.
            None => true,
        };

        let Some(proof) = proofs.get(name) else {
            if recorded_conf.is_none() && !recorded_broken {
                counts.unattempted += 1;
            } else {
                counts.missing_proof += 1;
            }
            continue;
        };
        match &proof.body {
            ProofBody::Skipped => unreachable!("read in Deps mode"),
            ProofBody::Unsupported(_) => {
                counts.unsupported += 1;
                continue;
            }
            ProofBody::Loaded(loaded) => {
                let seq = match project.load(path, name) {
                    Ok(seq) => seq,
                    Err(err) => {
                        counts.load_error += 1;
                        problems.push(format!("{component} {name}: {err}"));
                        continue;
                    }
                };
                let verdict = compute_status(&seq, proof);
                if !stamp_valid {
                    counts.stale += 1;
                    continue;
                }
                if verdict.context_dependent {
                    counts.context_dep += 1;
                    continue;
                }
                match (recorded_broken, verdict.broken) {
                    (true, true) => counts.broken_match += 1,
                    (false, false) => {
                        let computed = norm(verdict.confidence);
                        if recorded_conf == computed {
                            if computed.is_none() {
                                counts.unattempted += 1;
                            } else {
                                counts.matched += 1;
                                // The strongest check: apply every
                                // stored rule structurally and require
                                // the reused tree to reproduce the
                                // recorded confidence.
                                if let Some(skel) = &loaded.skeleton {
                                    let mut tree = ProofTreeNode::open(seq.clone());
                                    let complete = rossi_prove::builder::reuse(&mut tree, skel);
                                    let conf = tree.confidence();
                                    if complete && conf == Confidence(computed.unwrap_or(0)) {
                                        counts.reuse_ok += 1;
                                    } else {
                                        counts.diverge += 1;
                                        problems.push(format!(
                                            "{component} {name}: tree reuse {} at {conf:?},                                              recorded {computed:?}",
                                            if complete { "complete" } else { "incomplete" },
                                        ));
                                    }
                                }
                            }
                        } else {
                            counts.diverge += 1;
                            problems.push(format!(
                                "{component} {name}: recorded confidence {recorded_conf:?}, \
                                 computed {computed:?}"
                            ));
                        }
                    }
                    (false, true) => {
                        // Distrust caused purely by registry drift is a
                        // vintage effect: the row was never re-checked
                        // stamp-valid row.
                        if loaded
                            .deps
                            .used_reasoners
                            .iter()
                            .any(|desc| !desc.is_trusted())
                        {
                            counts.version_conflict += 1;
                        } else {
                            counts.diverge += 1;
                            let why = rossi_prove::deps::explain_reuse_failure(&loaded.deps, &seq)
                                .unwrap_or_default();
                            problems.push(format!(
                                "{component} {name}: recorded reusable, computed broken ({why})"
                            ));
                        }
                    }
                    (true, false) => {
                        // The recorded broken flag is the verdict of
                        // whatever toolchain vintage last re-checked
                        // (older WD-inclusion rules, a plugin-less
                        // install); the build-oracle gate decides these.
                        counts.broken_mismatch += 1;
                    }
                }
            }
        }
    }
}

#[test]
#[ignore = "needs a models corpus; run with --ignored"]
fn reuse_reproduces_recorded_statuses() {
    let Some(corpus) = corpus_dir() else {
        eprintln!("corpus not found; set EVENTB_CORPUS_DIR");
        return;
    };
    let flags = load_flags(&corpus.join("model_flags.tsv")).unwrap_or_default();
    let zips = collect_zips(&corpus).expect("corpus listing");

    let mut rows = Vec::new();
    let mut failures = Vec::new();
    let mut total = Counts::default();
    for path in &zips {
        let model = path
            .file_stem()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        if flagged_unsupported(&flags, &model) {
            rows.push(report_row(&model, &Counts::default(), "skip", "flagged"));
            continue;
        }
        let mut counts = Counts::default();
        let mut problems = Vec::new();
        if let Err(err) = check_model(path, &mut counts, &mut problems) {
            rows.push(report_row(&model, &counts, "skip", &err));
            continue;
        }
        let verdict = if counts.diverge > 0 || !problems.is_empty() {
            match prove_known_divergence(&corpus, &model) {
                Some(reason) => ("known", reason),
                None => {
                    failures.push(format!(
                        "{model}: {} divergences, first: {}",
                        counts.diverge.max(problems.len()),
                        problems.first().map(String::as_str).unwrap_or("?")
                    ));
                    ("diverge", problems.first().cloned().unwrap_or_default())
                }
            }
        } else {
            ("match", String::new())
        };
        rows.push(report_row(&model, &counts, verdict.0, &verdict.1));
        total.add(&counts);
    }

    let out = workspace_root().join("target/rossi-build-proof-reuse-corpus.tsv");
    write_report(
        &out,
        &[
            "model",
            "pos",
            "match",
            "broken_match",
            "unattempted",
            "stale",
            "context_dep",
            "version_conflict",
            "unsupported",
            "legacy",
            "load_error",
            "missing_proof",
            "broken_mismatch",
            "reuse_ok",
            "diverge",
            "verdict",
            "notes",
        ],
        &rows,
    );
    println!(
        "reuse: {} POs — {} match, {} broken_match, {} unattempted, {} stale, {} ctx, \
         {} version_conflict, {} unsupported, {} legacy, {} load_error, {} missing_proof, \
         {} broken_mismatch, {} reuse_ok, {} diverge; report: {}",
        total.pos,
        total.matched,
        total.broken_match,
        total.unattempted,
        total.stale,
        total.context_dep,
        total.version_conflict,
        total.unsupported,
        total.legacy,
        total.load_error,
        total.missing_proof,
        total.broken_mismatch,
        total.reuse_ok,
        total.diverge,
        out.display(),
    );
    assert!(
        failures.is_empty(),
        "{} models diverged:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

fn report_row(model: &str, counts: &Counts, verdict: &str, notes: &str) -> Vec<String> {
    vec![
        model.to_string(),
        counts.pos.to_string(),
        counts.matched.to_string(),
        counts.broken_match.to_string(),
        counts.unattempted.to_string(),
        counts.stale.to_string(),
        counts.context_dep.to_string(),
        counts.version_conflict.to_string(),
        counts.unsupported.to_string(),
        counts.legacy.to_string(),
        counts.load_error.to_string(),
        counts.missing_proof.to_string(),
        counts.broken_mismatch.to_string(),
        counts.reuse_ok.to_string(),
        counts.diverge.to_string(),
        verdict.to_string(),
        common::sanitize(notes),
    ]
}

fn check_model(path: &Path, counts: &mut Counts, problems: &mut Vec<String>) -> Result<(), String> {
    let file = std::fs::File::open(path).map_err(|err| err.to_string())?;
    let mut archive = zip::ZipArchive::new(file).map_err(|err| err.to_string())?;
    let names: Vec<String> = archive.file_names().map(str::to_string).collect();
    let mut read_entry = |name: &str| -> Option<Vec<u8>> {
        let mut bytes = Vec::new();
        archive.by_name(name).ok()?.read_to_end(&mut bytes).ok()?;
        Some(bytes)
    };
    let _ = BufReader::new(std::io::empty());

    let mut stems: Vec<String> = names
        .iter()
        .filter(|name| name.ends_with(".bpo"))
        .map(|name| name.trim_end_matches(".bpo").to_string())
        .collect();
    stems.sort();

    // First pass: parse every component's obligations, one project per
    // archive directory — hypothesis-set chains cross component files
    // within a project and resolve by file basename (archives are
    // routinely renamed, so handle paths keep the original project
    // name).
    let mut projects: BTreeMap<String, PoProject> = BTreeMap::new();
    let mut checked = Vec::new();
    for stem in &stems {
        let (dir, file) = stem.rsplit_once('/').unwrap_or(("", stem));
        let bpo =
            read_entry(&format!("{stem}.bpo")).ok_or_else(|| format!("unreadable {stem}.bpo"))?;
        let bpo = String::from_utf8_lossy(&bpo).into_owned();
        // Legacy obligation vintage: files predating the current
        // child-naming scheme are out of scope wholesale.
        if bpo.contains("name=\"GOAL\"") {
            let sequents = bpo.matches("<org.eventb.core.poSequent ").count();
            counts.pos += sequents;
            counts.legacy += sequents;
            continue;
        }
        match PoFile::read(bpo.as_bytes()) {
            Ok(parsed) => {
                projects
                    .entry(dir.to_string())
                    .or_default()
                    .insert(format!("{file}.bpo"), parsed);
                checked.push(stem.clone());
            }
            Err(err) => {
                counts.load_error += 1;
                problems.push(format!("{stem}: {err}"));
            }
        }
    }

    for stem in checked {
        let (dir, file) = stem.rsplit_once('/').unwrap_or(("", stem.as_str()));
        let bps = read_entry(&format!("{stem}.bps"));
        let bps = bps.as_deref().map(String::from_utf8_lossy);
        let bpr = read_entry(&format!("{stem}.bpr"));
        check_component(
            &projects[dir],
            &stem,
            &format!("{file}.bpo"),
            bps.as_deref(),
            bpr.as_deref(),
            counts,
            problems,
        );
    }
    Ok(())
}

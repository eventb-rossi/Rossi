//! `rossi prove` — check the stored proofs of an Event-B project
//! against its proof obligations.
//!
//! For every obligation in the input's `.bpo` files, the stored proof
//! in the sibling `.bpr` is checked by the dependency-based reuse
//! rule (the status-update decision): a proof that no longer applies to
//! its regenerated obligation reports as broken. The recorded `.bps`
//! statuses are not consulted — this command recomputes the verdicts.
//!
//! Any broken or uncheckable proof makes the exit code nonzero;
//! pending and unattempted obligations do not: open proofs are work
//! in progress rather than errors.
//!
//! With `--replay`, every checkable proof whose reasoners are all
//! implemented is additionally re-derived: each reasoner is re-run on
//! its recorded input and the reconstructed tree must complete
//! (the replay mode). Proofs using reasoners without a Rust
//! implementation are skipped, not failed — coverage grows with the
//! reasoner batches — while a replay that fails on an implemented
//! proof is an error.

use std::collections::BTreeMap;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Args;

use rossi_prove::bpr::{Keep, ProofBody, ProofEntry, read_bpr};
use rossi_prove::po_loader::{PoFile, PoProject};
use rossi_prove::status::compute_status;
use rossi_prove::{ProofTreeNode, ReasonerProvider, RegistryProvider, Skeleton};

#[derive(Args)]
pub struct ProveArgs {
    /// Input to check: an Event-B `.zip` archive or a project directory
    /// containing `.bpo` / `.bpr` files.
    pub input: PathBuf,
    /// Also list every checked obligation, not only the problematic
    /// ones.
    #[arg(short, long)]
    pub verbose: bool,
    /// Re-run each proof's reasoners on their recorded inputs and
    /// require the reconstructed tree to complete (proofs using
    /// unimplemented reasoners are skipped).
    #[arg(long)]
    pub replay: bool,
}

#[derive(Default)]
struct Summary {
    discharged: usize,
    reviewed: usize,
    pending: usize,
    unattempted: usize,
    broken: usize,
    unsupported: usize,
    errors: usize,
    replayed: usize,
    replay_skipped: usize,
    replay_failed: usize,
}

pub fn run(args: ProveArgs) -> ExitCode {
    match prove(&args.input, args.verbose, args.replay) {
        Ok(summary) => {
            let total = summary.discharged
                + summary.reviewed
                + summary.pending
                + summary.unattempted
                + summary.broken
                + summary.unsupported
                + summary.errors;
            println!(
                "Proofs: {total} obligation(s) — {} discharged, {} reviewed, {} pending, \
                 {} unattempted, {} broken, {} unsupported, {} error(s)",
                summary.discharged,
                summary.reviewed,
                summary.pending,
                summary.unattempted,
                summary.broken,
                summary.unsupported,
                summary.errors,
            );
            if args.replay {
                println!(
                    "Replay: {} replayed, {} skipped (unimplemented reasoners), {} failed",
                    summary.replayed, summary.replay_skipped, summary.replay_failed,
                );
            }
            if summary.broken + summary.unsupported + summary.errors + summary.replay_failed > 0 {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(e) => {
            eprintln!("rossi prove: {e}");
            ExitCode::from(1)
        }
    }
}

/// The first stored reasoner in the skeleton without an implementation,
/// making the proof unreplayable for now.
fn missing_reasoner(skel: &Skeleton) -> Option<String> {
    let mut stack = vec![skel];
    while let Some(node) = stack.pop() {
        if let Some(stored) = &node.rule {
            if RegistryProvider
                .implementation(&stored.rule.reasoner)
                .is_none()
            {
                return Some(stored.rule.reasoner.id().to_string());
            }
        }
        stack.extend(node.children.iter());
    }
    None
}

/// The `(component stem, contents)` of every file with `extension`
/// in the input, stems keeping their archive directory prefix.
type FileMap = BTreeMap<String, Vec<u8>>;

fn prove(input: &Path, verbose: bool, replay: bool) -> Result<Summary, Box<dyn std::error::Error>> {
    let (bpos, bprs) = collect(input)?;
    let keep = if replay { Keep::Full } else { Keep::Deps };

    // One project per archive directory: hypothesis-set chains cross
    // component files and resolve by file basename.
    let mut projects: BTreeMap<&str, PoProject> = BTreeMap::new();
    for (stem, contents) in &bpos {
        let (dir, file) = stem.rsplit_once('/').unwrap_or(("", stem));
        let parsed =
            PoFile::read(contents.as_slice()).map_err(|err| format!("{stem}.bpo: {err}"))?;
        projects
            .entry(dir)
            .or_default()
            .insert(format!("{file}.bpo"), parsed);
    }

    let mut summary = Summary::default();
    for stem in bpos.keys() {
        let (dir, file) = stem.rsplit_once('/').unwrap_or(("", stem.as_str()));
        let project = &projects[dir];
        let path = format!("{file}.bpo");
        let Some(po) = project.file(&path) else {
            continue;
        };
        let proofs: BTreeMap<String, ProofEntry> = match bprs.get(stem) {
            Some(bytes) => match read_bpr(bytes.as_slice(), |_| keep) {
                Ok(entries) => entries
                    .into_iter()
                    .map(|entry| (entry.name.clone(), entry))
                    .collect(),
                Err(err) => {
                    println!("{stem}: unreadable proof file: {err}");
                    summary.errors += po.sequents().count();
                    continue;
                }
            },
            None => BTreeMap::new(),
        };
        for entry in po.sequents() {
            let name = &entry.name;
            let mut note = String::new();
            let status = match proofs.get(name) {
                None => "unattempted",
                Some(proof) => match &proof.body {
                    ProofBody::Skipped => unreachable!("every proof is read"),
                    ProofBody::Unsupported(_) => "unsupported",
                    ProofBody::Loaded(stored) => match project.load(&path, name) {
                        Err(_) => "error",
                        Ok(seq) => {
                            let verdict = compute_status(&seq, proof);
                            if replay && !verdict.broken {
                                let skel = stored.skeleton.as_ref().expect("full parse");
                                note = match missing_reasoner(skel) {
                                    Some(id) => {
                                        summary.replay_skipped += 1;
                                        format!(" (replay skipped: {id})")
                                    }
                                    None => {
                                        let mut node = ProofTreeNode::open(seq.clone());
                                        if rossi_prove::replay(&mut node, skel, &RegistryProvider) {
                                            summary.replayed += 1;
                                            " (replayed)".into()
                                        } else {
                                            summary.replay_failed += 1;
                                            " (replay FAILED)".into()
                                        }
                                    }
                                };
                            }
                            if verdict.broken {
                                "broken"
                            } else {
                                match verdict.confidence {
                                    Some(c) if c > 500 => "discharged",
                                    Some(c) if c > 100 => "reviewed",
                                    Some(c) if c > -99 => "pending",
                                    _ => "unattempted",
                                }
                            }
                        }
                    },
                },
            };
            match status {
                "discharged" => summary.discharged += 1,
                "reviewed" => summary.reviewed += 1,
                "pending" => summary.pending += 1,
                "unattempted" => summary.unattempted += 1,
                "broken" => summary.broken += 1,
                "unsupported" => summary.unsupported += 1,
                _ => summary.errors += 1,
            }
            if verbose
                || matches!(status, "broken" | "unsupported" | "error")
                || note.contains("FAILED")
            {
                println!("{stem} {name}: {status}{note}");
            }
        }
    }
    Ok(summary)
}

/// Collects the `.bpo` and `.bpr` files of a `.zip` archive or a
/// project directory, keyed by component stem.
fn collect(input: &Path) -> Result<(FileMap, FileMap), Box<dyn std::error::Error>> {
    let mut bpos = FileMap::new();
    let mut bprs = FileMap::new();
    if input.is_dir() {
        for entry in std::fs::read_dir(input)? {
            let path = entry?.path();
            let (Some(stem), Some(ext)) = (
                path.file_stem().and_then(|s| s.to_str()),
                path.extension().and_then(|s| s.to_str()),
            ) else {
                continue;
            };
            match ext {
                "bpo" => {
                    bpos.insert(stem.to_string(), std::fs::read(&path)?);
                }
                "bpr" => {
                    bprs.insert(stem.to_string(), std::fs::read(&path)?);
                }
                _ => {}
            }
        }
    } else {
        let file = std::fs::File::open(input)?;
        let mut archive = zip::ZipArchive::new(file)?;
        for index in 0..archive.len() {
            let mut entry = archive.by_index(index)?;
            let name = entry.name().to_string();
            let Some((stem, ext)) = name.rsplit_once('.') else {
                continue;
            };
            if ext != "bpo" && ext != "bpr" {
                continue;
            }
            let mut bytes = Vec::new();
            entry.read_to_end(&mut bytes)?;
            if ext == "bpo" {
                bpos.insert(stem.to_string(), bytes);
            } else {
                bprs.insert(stem.to_string(), bytes);
            }
        }
    }
    if bpos.is_empty() {
        return Err(format!("no .bpo files found in {}", input.display()).into());
    }
    Ok((bpos, bprs))
}

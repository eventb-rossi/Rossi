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
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Args;

use rossi_prove::bpr::{Keep, ProofBody, ProofEntry, read_bpr};
use rossi_prove::confidence::Bucket;
use rossi_prove::po_loader::{PoFile, PoProject};
use rossi_prove::status::compute_status;
use rossi_prove::{Confidence, ProofTreeNode, ReasonerProvider, RegistryProvider, Skeleton};

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
            let mut replay_failed = false;
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
                                            replay_failed = true;
                                            " (replay FAILED)".into()
                                        }
                                    }
                                };
                            }
                            if verdict.broken {
                                "broken"
                            } else {
                                match Confidence::classify(verdict.confidence.map(i64::from)) {
                                    Bucket::Discharged => "discharged",
                                    Bucket::Reviewed => "reviewed",
                                    Bucket::Pending => "pending",
                                    Bucket::Unattempted => "unattempted",
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
            if verbose || matches!(status, "broken" | "unsupported" | "error") || replay_failed {
                println!("{stem} {name}: {status}{note}");
            }
        }
    }
    Ok(summary)
}

/// Collects the `.bpo` and `.bpr` files of a `.zip` archive or a
/// project directory, keyed by component stem — through the shared
/// proof-file walkers, so the extension set and the unsafe-basename
/// filter stay in one place.
fn collect(input: &Path) -> Result<(FileMap, FileMap), Box<dyn std::error::Error>> {
    let mut bpos = FileMap::new();
    let mut bprs = FileMap::new();
    let mut insert = |name: &str, bytes: Vec<u8>| {
        if let Some((stem, ext)) = name.rsplit_once('.') {
            match ext {
                "bpo" => {
                    bpos.insert(stem.to_string(), bytes);
                }
                "bpr" => {
                    bprs.insert(stem.to_string(), bytes);
                }
                _ => {}
            }
        }
    };
    if input.is_dir() {
        for (basename, bytes) in super::proofs::proofs_in_dir(input)? {
            insert(&basename, bytes);
        }
    } else {
        let bytes = std::fs::read(input)?;
        super::proofs::visit_zip_proofs(
            &bytes,
            |_| true,
            |name, bytes| {
                insert(name, bytes);
                Ok(())
            },
        )?;
    }
    if bpos.is_empty() {
        return Err(format!("no .bpo files found in {}", input.display()).into());
    }
    Ok((bpos, bprs))
}

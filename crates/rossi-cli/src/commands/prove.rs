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

use std::collections::BTreeMap;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Args;

use rossi_prove::bpr::{Keep, ProofBody, ProofEntry, read_bpr};
use rossi_prove::po_loader::{PoFile, PoProject};
use rossi_prove::status::compute_status;

#[derive(Args)]
pub struct ProveArgs {
    /// Input to check: an Event-B `.zip` archive or a project directory
    /// containing `.bpo` / `.bpr` files.
    pub input: PathBuf,
    /// Also list every checked obligation, not only the problematic
    /// ones.
    #[arg(short, long)]
    pub verbose: bool,
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
}

pub fn run(args: ProveArgs) -> ExitCode {
    match prove(&args.input, args.verbose) {
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
            if summary.broken + summary.unsupported + summary.errors > 0 {
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

/// The `(component stem, contents)` of every file with `extension`
/// in the input, stems keeping their archive directory prefix.
type FileMap = BTreeMap<String, Vec<u8>>;

fn prove(input: &Path, verbose: bool) -> Result<Summary, Box<dyn std::error::Error>> {
    let (bpos, bprs) = collect(input)?;

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
            Some(bytes) => match read_bpr(bytes.as_slice(), |_| Keep::Deps) {
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
            let status = match proofs.get(name) {
                None => "unattempted",
                Some(proof) => match &proof.body {
                    ProofBody::Skipped => unreachable!("read in Deps mode"),
                    ProofBody::Unsupported(_) => "unsupported",
                    ProofBody::Loaded(_) => match project.load(&path, name) {
                        Err(_) => "error",
                        Ok(seq) => {
                            let verdict = compute_status(&seq, proof);
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
            if verbose || matches!(status, "broken" | "unsupported" | "error") {
                println!("{stem} {name}: {status}");
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

//! Build a text source directory into the shared Rodin project directory.
//!
//! Mirrors the CLI's `rossi build <dir> -o <dir>` pipeline (parse text →
//! serialize → static-check → reconcile → write), with two differences owed
//! to living inside the language server: unsaved editor buffers overlay the
//! on-disk sources, and the destination is a *persistent* Rodin project the
//! user proves in — so generated `.bpo`/`.bps` reconcile against whatever is
//! on disk there (Rodin's own stamps and statuses carry over for unchanged
//! obligations) and `.bpr` proof files are never written, pruned, or touched.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use rossi::{NamedComponent, component_filename, parse_components, to_zip, write_project_directory};
use rossi_build::pog::reconcile::reconcile_build_files;
use rossi_build::project::discover_projects;
use rossi_build::{Severity, build};

/// What a project build left behind, for user-facing reporting.
#[derive(Debug)]
pub struct BuildOutcome {
    /// Generated files written into the project directory (`.bcc`/`.bcm`/
    /// `.bpo`/`.bps`; sources and `.project` are written besides these).
    pub files_written: usize,
    /// Rendered error diagnostics. Non-empty means the checked output was
    /// still written, with erroneous elements dropped (Rodin semantics).
    pub error_diagnostics: Vec<String>,
}

/// Text buffers overlaying the filesystem, keyed by canonicalized path.
pub type Overlay = HashMap<PathBuf, String>;

/// Collect the `.eventb`/`.txt` sources under `dir` (recursively, skipping
/// dot-directories such as the `.rossi` workspace itself), sorted.
pub fn collect_source_files(dir: &Path) -> std::io::Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    for entry in walkdir::WalkDir::new(dir)
        .follow_links(true)
        .max_depth(64)
        .into_iter()
        .filter_entry(|entry| {
            entry.depth() == 0
                || !(entry.file_type().is_dir()
                    && entry
                        .file_name()
                        .to_str()
                        .is_some_and(|name| name.starts_with('.')))
        })
    {
        let entry = entry.map_err(std::io::Error::other)?;
        if entry.file_type().is_file()
            && matches!(
                entry.path().extension().and_then(|e| e.to_str()),
                Some("eventb") | Some("txt")
            )
        {
            files.push(entry.path().to_path_buf());
        }
    }
    files.sort();
    Ok(files)
}

/// Read a source file, preferring the editor's in-memory text when the file
/// is open (matched via canonicalized paths).
fn read_with_overlay(path: &Path, overlay: &Overlay) -> std::io::Result<String> {
    let canonical = std::fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    if let Some(text) = overlay.get(&canonical) {
        return Ok(text.clone());
    }
    std::fs::read_to_string(path)
}

/// Build every Event-B text source under `source_dir` into the Rodin project
/// at `project_dir`: sources + `.project` via the exporter, checked files and
/// proof obligations via the static checker, `.bpo`/`.bps` reconciled against
/// the files being replaced so proof state Rodin wrote there survives.
pub fn build_rodin_project(
    source_dir: &Path,
    overlay: &Overlay,
    project_dir: &Path,
    project_name: &str,
) -> Result<BuildOutcome, String> {
    let sources =
        collect_source_files(source_dir).map_err(|e| format!("cannot scan {}: {e}", source_dir.display()))?;
    if sources.is_empty() {
        return Err(format!("no Event-B files found in {}", source_dir.display()));
    }

    let mut components: Vec<NamedComponent> = Vec::new();
    for path in &sources {
        let text = read_with_overlay(path, overlay)
            .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
        let parsed =
            parse_components(&text).map_err(|e| format!("failed to parse {}: {e}", path.display()))?;
        components.extend(parsed.into_iter().map(|component| NamedComponent {
            filename: component_filename(&component),
            component,
        }));
    }

    // A duplicate component name cannot be serialized (its name is its
    // filename) and the project is invalid regardless; fail before touching
    // the destination.
    let mut seen = std::collections::BTreeSet::new();
    for nc in &components {
        if !seen.insert(nc.component.name().to_string()) {
            return Err(format!(
                "duplicate component name '{}' across the source files",
                nc.component.name()
            ));
        }
    }

    let bytes = to_zip(&components).map_err(|e| format!("cannot serialize project: {e}"))?;
    let projects =
        discover_projects(&bytes, project_name).map_err(|e| format!("cannot assemble project: {e}"))?;
    let Some(discovered) = projects.into_iter().next() else {
        return Err("no Event-B project could be assembled from the sources".to_string());
    };
    let result = build(&discovered.into_project());
    if result.failed_outright() {
        let rendered: Vec<String> = result.diagnostics.iter().map(|d| d.to_string()).collect();
        return Err(format!(
            "the project produced no checked output:\n{}",
            rendered.join("\n")
        ));
    }

    // Write sources + `.project` first so the generated files land next to
    // them; the exporter creates the directory.
    write_project_directory(project_dir, &components, project_name)
        .map_err(|e| format!("cannot write project into {}: {e}", project_dir.display()))?;

    let mut files = result.files;
    for f in &files {
        if !is_normal_path_component(&f.filename) {
            return Err(format!("unsafe generated filename {:?}", f.filename));
        }
    }
    // Previous state comes from the destination — the files being replaced —
    // which is where Rodin recorded its stamps and proof statuses.
    reconcile_build_files(&mut files, |name| {
        std::fs::read_to_string(project_dir.join(name)).ok()
    });
    for f in &files {
        std::fs::write(project_dir.join(&f.filename), &f.contents)
            .map_err(|e| format!("cannot write {}: {e}", f.filename))?;
    }

    prune_stale_generated_files(project_dir, &components, &files);

    Ok(BuildOutcome {
        files_written: files.len(),
        error_diagnostics: result
            .diagnostics
            .iter()
            .filter(|d| d.severity == Severity::Error)
            .map(|d| d.to_string())
            .collect(),
    })
}

/// Remove generated/source files a previous build wrote for components that
/// no longer exist (renamed or deleted). Only rossi's own file kinds are
/// candidates — `.bpr` proofs and anything else Rodin keeps in the project
/// are never touched. Best effort.
fn prune_stale_generated_files(
    project_dir: &Path,
    components: &[NamedComponent],
    generated: &[rossi_build::ScFile],
) {
    let expected: std::collections::BTreeSet<&str> = components
        .iter()
        .map(|nc| nc.filename.as_str())
        .chain(generated.iter().map(|f| f.filename.as_str()))
        .collect();
    let Ok(entries) = std::fs::read_dir(project_dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if !path.is_file() {
            continue;
        }
        let stale = matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("buc" | "bum" | "bcc" | "bcm" | "bpo" | "bps")
        ) && path
            .file_name()
            .and_then(|n| n.to_str())
            .is_some_and(|name| !expected.contains(name));
        if stale && let Err(e) = std::fs::remove_file(&path) {
            tracing::info!("could not prune stale {}: {e}", path.display());
        }
    }
}

fn is_normal_path_component(value: &str) -> bool {
    if value.contains('\0') {
        return false;
    }
    let path = Path::new(value);
    let mut parts = path.components();
    matches!(parts.next(), Some(std::path::Component::Normal(part)) if path.as_os_str() == part)
        && parts.next().is_none()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_dir(prefix: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "{prefix}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    const CTX: &str = "CONTEXT base_ctx\nCONSTANTS\n    lo\nAXIOMS\n    @axm1 lo ∈ ℤ\nEND\n";

    #[test]
    fn builds_a_full_rodin_project_from_text() {
        let root = temp_dir("rossi-rodin-build-test");
        let src = root.join("src");
        std::fs::create_dir_all(&src).unwrap();
        std::fs::write(src.join("base_ctx.eventb"), CTX).unwrap();
        let project = root.join("ws").join("src");

        let outcome =
            build_rodin_project(&src, &Overlay::new(), &project, "src").expect("build succeeds");

        assert!(outcome.error_diagnostics.is_empty());
        assert!(project.join(".project").is_file());
        assert!(project.join("base_ctx.buc").is_file());
        assert!(project.join("base_ctx.bcc").is_file());
        assert!(project.join("base_ctx.bpo").is_file());
        assert!(project.join("base_ctx.bps").is_file());
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn overlay_text_wins_over_disk() {
        let root = temp_dir("rossi-rodin-overlay-test");
        let src = root.join("src");
        std::fs::create_dir_all(&src).unwrap();
        let file = src.join("base_ctx.eventb");
        std::fs::write(&file, CTX).unwrap();
        let project = root.join("ws").join("src");

        let mut overlay = Overlay::new();
        overlay.insert(
            std::fs::canonicalize(&file).unwrap(),
            CTX.replace("base_ctx", "buffer_ctx"),
        );
        build_rodin_project(&src, &overlay, &project, "src").expect("build succeeds");

        assert!(project.join("buffer_ctx.buc").is_file());
        assert!(!project.join("base_ctx.buc").exists());
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn rebuild_prunes_stale_components_but_never_proofs() {
        let root = temp_dir("rossi-rodin-prune-test");
        let src = root.join("src");
        std::fs::create_dir_all(&src).unwrap();
        let file = src.join("model.eventb");
        std::fs::write(&file, CTX).unwrap();
        let project = root.join("ws").join("src");

        build_rodin_project(&src, &Overlay::new(), &project, "src").unwrap();
        std::fs::write(project.join("base_ctx.bpr"), "PROOFS").unwrap();

        // Rename the component; the old component's files must be pruned,
        // while the `.bpr` (even the now-orphaned one) stays untouched.
        std::fs::write(&file, CTX.replace("base_ctx", "renamed_ctx")).unwrap();
        build_rodin_project(&src, &Overlay::new(), &project, "src").unwrap();

        assert!(project.join("renamed_ctx.buc").is_file());
        assert!(!project.join("base_ctx.buc").exists());
        assert!(!project.join("base_ctx.bpo").exists());
        assert_eq!(
            std::fs::read_to_string(project.join("base_ctx.bpr")).unwrap(),
            "PROOFS"
        );
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn rebuild_preserves_reconciled_statuses() {
        let root = temp_dir("rossi-rodin-reconcile-test");
        let src = root.join("src");
        std::fs::create_dir_all(&src).unwrap();
        // A machine with an invariant yields at least one obligation row.
        std::fs::write(
            src.join("m.eventb"),
            "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x ∈ ℕ\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        x ≔ 0\n    END\nEND\n",
        )
        .unwrap();
        let project = root.join("ws").join("src");

        build_rodin_project(&src, &Overlay::new(), &project, "src").unwrap();
        let bps = project.join("m.bps");
        let first = std::fs::read_to_string(&bps).unwrap();
        // Doctor one status row the way a prover run would: mark it discharged.
        let doctored = first.replace("confidence=\"-99\"", "confidence=\"1000\"");
        assert_ne!(first, doctored, "fixture must contain an unattempted row");
        std::fs::write(&bps, &doctored).unwrap();

        build_rodin_project(&src, &Overlay::new(), &project, "src").unwrap();
        assert_eq!(
            std::fs::read_to_string(&bps).unwrap(),
            doctored,
            "an unchanged model must carry its proof statuses across rebuilds"
        );
        std::fs::remove_dir_all(&root).ok();
    }

    #[test]
    fn duplicate_component_names_fail_before_writing() {
        let root = temp_dir("rossi-rodin-dup-test");
        let src = root.join("src");
        std::fs::create_dir_all(&src).unwrap();
        std::fs::write(src.join("a.eventb"), "MACHINE M\nEND\n").unwrap();
        std::fs::write(src.join("b.eventb"), "MACHINE M\nEND\n").unwrap();
        let project = root.join("ws").join("src");

        let err = build_rodin_project(&src, &Overlay::new(), &project, "src").unwrap_err();
        assert!(err.contains("duplicate component name"), "{err}");
        assert!(!project.exists(), "nothing may be written on failure");
        std::fs::remove_dir_all(&root).ok();
    }
}

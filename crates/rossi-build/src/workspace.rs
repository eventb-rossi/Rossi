//! The shared Rodin workspace: where it lives and how projects inside it
//! are named.
//!
//! The language server builds models into a persistent Rodin workspace —
//! by default `<root>/.rossi/rodin` — with one project per source
//! directory. The naming convention here is the single source of truth for
//! that layout: the LSP creates project directories with it, and
//! out-of-process consumers (the `rossi` CLI's proof discovery) locate the
//! same directories by reapplying it.

use std::path::{Path, PathBuf};

/// Default shared workspace location, relative to the LSP workspace root
/// (or, in single-file mode, the document's directory).
pub fn default_workspace_dir(root: &Path) -> PathBuf {
    root.join(".rossi").join("rodin")
}

/// An Eclipse-safe project name derived from a directory or file stem:
/// mirror of the extension's former `rodinProjectName`.
pub fn sanitize_project_name(input: &str) -> String {
    let sanitized: String = input
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-') {
                c
            } else {
                '_'
            }
        })
        .collect();
    let trimmed = sanitized.trim_start_matches(['.', '-']);
    if trimmed.is_empty() {
        "rossi_project".to_string()
    } else {
        trimmed.to_string()
    }
}

/// A stable, collision-free project name for a source directory.
///
/// Inside the workspace root the name is the sanitized root-relative path
/// joined with underscores, so sibling directories sharing a basename get
/// distinct projects and the name stays readable. The root itself keeps
/// its basename. A directory outside any known root falls back to its
/// basename plus a stable hash of its absolute path.
pub fn project_name_for(source_dir: &Path, workspace_root: Option<&Path>) -> String {
    if let Some(root) = workspace_root
        && let Ok(relative) = source_dir.strip_prefix(root)
    {
        let joined = relative
            .components()
            .filter_map(|c| match c {
                std::path::Component::Normal(part) => part.to_str(),
                _ => None,
            })
            .collect::<Vec<_>>()
            .join("_");
        if joined.is_empty() {
            // The workspace root itself.
            return sanitize_project_name(
                root.file_name()
                    .and_then(|s| s.to_str())
                    .unwrap_or_default(),
            );
        }
        return sanitize_project_name(&joined);
    }
    let base = sanitize_project_name(
        source_dir
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or_default(),
    );
    format!("{base}-{:08x}", stable_path_hash(source_dir))
}

/// FNV-1a over the path bytes. Deliberately not `DefaultHasher`, whose
/// output may change across toolchains — the name must stay stable so the
/// project (and the proofs Rodin stored in it) survives server upgrades.
fn stable_path_hash(path: &Path) -> u32 {
    let mut hash: u32 = 0x811c_9dc5;
    for byte in path.as_os_str().as_encoded_bytes() {
        hash ^= u32::from(*byte);
        hash = hash.wrapping_mul(0x0100_0193);
    }
    hash
}

/// The Rodin project directory for a text source directory, if the shared
/// workspace exists — the reverse of [`default_workspace_dir`] +
/// [`project_name_for`], for out-of-process callers (the `rossi` CLI) that
/// cannot see a `rossi.rodin.workspace` editor-config override: walk up to
/// the nearest ancestor holding `.rossi/rodin`, then apply the naming
/// convention.
///
/// The LSP names projects from the editor's raw (uncanonicalized) paths, so
/// the raw absolute path is tried first and its canonicalized form second —
/// under a symlinked checkout the two derive different project names, and
/// only the raw one matches the directory the LSP actually created.
pub fn workspace_project_dir(source_dir: &Path) -> Option<PathBuf> {
    let raw = if source_dir.is_absolute() {
        Some(source_dir.to_path_buf())
    } else {
        std::env::current_dir().ok().map(|cwd| cwd.join(source_dir))
    };
    let mut candidates: Vec<PathBuf> = raw.into_iter().collect();
    if let Ok(canon) = std::fs::canonicalize(source_dir)
        && !candidates.contains(&canon)
    {
        candidates.push(canon);
    }
    for path in candidates {
        let Some(root) = path
            .ancestors()
            .find(|a| a.join(".rossi").join("rodin").is_dir())
        else {
            continue;
        };
        let project_dir = default_workspace_dir(root).join(project_name_for(&path, Some(root)));
        if project_dir.is_dir() {
            return Some(project_dir);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scratch_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("rossi-build-{name}-{}", std::process::id()));
        std::fs::remove_dir_all(&dir).ok();
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn sanitizes_project_names() {
        assert_eq!(sanitize_project_name("cars on bridge"), "cars_on_bridge");
        assert_eq!(sanitize_project_name("..--weird"), "weird");
        assert_eq!(sanitize_project_name("...."), "rossi_project");
        assert_eq!(sanitize_project_name("ok-1.2_x"), "ok-1.2_x");
    }

    #[test]
    fn project_names_are_scoped_to_the_workspace_root() {
        let root = Path::new("/proj");
        assert_eq!(
            project_name_for(Path::new("/proj/models/lift/src"), Some(root)),
            "models_lift_src"
        );
        // Directories sharing a basename never collide.
        assert_ne!(
            project_name_for(Path::new("/proj/a/model"), Some(root)),
            project_name_for(Path::new("/proj/b/model"), Some(root))
        );
        // The root itself keeps its basename.
        assert_eq!(project_name_for(root, Some(root)), "proj");
        // Outside any root: basename plus a stable path hash.
        let outside = project_name_for(Path::new("/elsewhere/model"), Some(root));
        assert!(outside.starts_with("model-"), "{outside}");
        assert_eq!(
            outside,
            project_name_for(Path::new("/elsewhere/model"), Some(root)),
            "the fallback name must be stable"
        );
        assert_ne!(outside, project_name_for(Path::new("/other/model"), None));
    }

    #[test]
    fn default_workspace_is_dot_rossi_rodin() {
        assert_eq!(
            default_workspace_dir(Path::new("/proj")),
            PathBuf::from("/proj/.rossi/rodin")
        );
    }

    #[test]
    fn workspace_walkup_names_nested_dirs_by_relative_path() {
        let tmp = scratch_dir("workspace-walkup");
        let nested = tmp.join("models").join("lift");
        std::fs::create_dir_all(&nested).unwrap();
        let project = tmp.join(".rossi").join("rodin").join("models_lift");
        std::fs::create_dir_all(&project).unwrap();
        assert_eq!(workspace_project_dir(&nested), Some(project));
    }

    #[cfg(unix)]
    #[test]
    fn workspace_lookup_prefers_the_raw_symlinked_path() {
        // The checkout really lives at `target`, but the LSP saw it through
        // the `link` symlink and named the project after the raw path — so
        // the lookup must derive the name from the raw path too; a
        // canonicalize-first lookup would derive "target" and find nothing.
        let tmp = scratch_dir("workspace-symlink");
        let target = tmp.join("target");
        std::fs::create_dir_all(target.join(".rossi").join("rodin").join("link")).unwrap();
        let link = tmp.join("link");
        std::os::unix::fs::symlink(&target, &link).unwrap();
        assert_eq!(
            workspace_project_dir(&link),
            Some(link.join(".rossi").join("rodin").join("link"))
        );
    }
}

//! The one definition of how Event-B source trees are walked.
//!
//! Every consumer of a source tree — the LSP's workspace index, the Rodin
//! build, and the `rossi` CLI — must agree on what the tree contains: if
//! they diverge (one descends into `.rossi/rodin`, the other does not), the
//! index and the built project disagree and phantom duplicate-component
//! diagnostics appear. Any refinement to the walk (new skip rules, depth
//! policy) belongs here, once.

use std::ffi::OsStr;
use std::path::Path;

/// A dot-named path component (`.git`, the `.rossi/rodin` Rodin workspace,
/// Eclipse `.metadata`), which holds generated or foreign files, never
/// Event-B sources.
fn is_hidden_name(name: &OsStr) -> bool {
    name.to_str().is_some_and(|name| name.starts_with('.'))
}

/// A directory entry to skip: a dot-named directory.
fn is_hidden_dir(entry: &walkdir::DirEntry) -> bool {
    entry.file_type().is_dir() && is_hidden_name(entry.file_name())
}

/// The extension every Event-B source file carries. Exposed for the client
/// watcher glob (`**/*.eventb`), the one consumer that needs the bare
/// extension rather than [`is_source_file`].
pub const SOURCE_EXTENSION: &str = "eventb";

/// Whether `path` names an Event-B source file. The extension half of what
/// [`source_walk`] yields, which that walk deliberately leaves to its callers
/// so they can pair it with their own containment rule.
///
/// Only `.eventb`: `.txt` is too generic to pick up from a directory — a
/// `README.txt` is not a component — though the CLI still validates a `.txt`
/// a user names explicitly.
pub fn is_source_file(path: &Path) -> bool {
    path.extension().and_then(OsStr::to_str) == Some(SOURCE_EXTENSION)
}

/// Walk a source tree the way every Event-B consumer does: symlinks are
/// followed (Rodin workspaces commonly link shared model directories) with
/// a depth cap keeping linked runaway trees bounded (walkdir's loop
/// detection handles cycles), and dot-directories are never descended
/// into. Callers filter by extension themselves.
pub fn source_walk(root: &Path) -> impl Iterator<Item = walkdir::Result<walkdir::DirEntry>> {
    walkdir::WalkDir::new(root)
        .follow_links(true)
        .max_depth(64)
        .into_iter()
        .filter_entry(|entry| entry.depth() == 0 || !is_hidden_dir(entry))
}

/// Whether `path` lies lexically under `root` with no dot-named directory
/// between them — [`source_walk`]'s skip rule, applied to one path instead of
/// a tree. It does not model the walk's symlink resolution or depth cap, so it
/// is a slightly wider answer than actually walking would give.
///
/// A client's file watcher reports every match of its glob, including the
/// generated trees the walk skips, so watched-file events must be filtered
/// through the same rule — otherwise a `.rossi/rodin` copy of a component
/// enters the index the scan would never have put it in, and the phantom
/// duplicate-component diagnostics this module exists to prevent appear
/// anyway. A `path` outside `root` is rejected: the index only ever mirrors
/// the scanned tree. Pair it with [`is_source_file`] for the whole rule.
pub fn is_within_source_walk(root: &Path, path: &Path) -> bool {
    let Ok(relative) = path.strip_prefix(root) else {
        return false;
    };
    // Only the directories above the file are subject to the dot rule; a
    // dot-named *file* is a source like any other, and `root` itself may
    // sit anywhere (a checkout under `~/.config` stays walkable).
    !relative
        .components()
        .rev()
        .skip(1)
        .any(|component| is_hidden_name(component.as_os_str()))
}

#[cfg(test)]
mod tests {
    use super::{is_source_file, is_within_source_walk};
    use std::path::Path;

    #[test]
    fn recognises_only_the_eventb_extension() {
        assert!(is_source_file(Path::new("/models/machine.eventb")));
        assert!(!is_source_file(Path::new("/models/machine.bum")));
        assert!(!is_source_file(Path::new("/models/machine")));
    }

    #[test]
    fn accepts_a_source_below_the_root() {
        assert!(is_within_source_walk(
            Path::new("/models"),
            Path::new("/models/sub/machine.eventb")
        ));
    }

    #[test]
    fn rejects_a_source_under_a_dot_directory() {
        assert!(!is_within_source_walk(
            Path::new("/models"),
            Path::new("/models/.rossi/rodin/machine.eventb")
        ));
    }

    #[test]
    fn rejects_a_path_outside_the_root() {
        assert!(!is_within_source_walk(
            Path::new("/models"),
            Path::new("/elsewhere/machine.eventb")
        ));
    }

    #[test]
    fn accepts_a_source_under_a_dot_named_root() {
        assert!(is_within_source_walk(
            Path::new("/home/u/.config/models"),
            Path::new("/home/u/.config/models/machine.eventb")
        ));
    }
}

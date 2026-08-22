//! The one definition of how Event-B source trees are walked.
//!
//! Every consumer of a source tree — the LSP's workspace index, the Rodin
//! build, and the `rossi` CLI — must agree on what the tree contains: if
//! they diverge (one descends into `.rossi/rodin`, the other does not), the
//! index and the built project disagree and phantom duplicate-component
//! diagnostics appear. Any refinement to the walk (new skip rules, depth
//! policy) belongs here, once.

use std::path::Path;

/// A directory entry for a dot-named directory (`.git`, the `.rossi/rodin`
/// Rodin workspace, Eclipse `.metadata`), which holds generated or foreign
/// files, never Event-B sources.
pub fn is_hidden_dir(entry: &walkdir::DirEntry) -> bool {
    entry.file_type().is_dir()
        && entry
            .file_name()
            .to_str()
            .is_some_and(|name| name.starts_with('.'))
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

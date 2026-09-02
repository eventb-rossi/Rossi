//! One answer to "are these two URIs the same file?".
//!
//! A file reaches the server under more than one spelling: the workspace scan
//! builds its URI from a `walkdir` path, the client sends whatever it opened,
//! and the two can differ in percent-encoding, in case, or by a symlink. An
//! index that keys on the raw string then holds one file twice — which reads
//! as two files declaring the same component, i.e. a phantom duplicate.
//!
//! Both workspace indexes share one of these, so they agree on file identity
//! as well as on file content. Note `DocumentManager` still canonicalizes
//! paths of its own (`open_file_texts`, `open_document_by_path`); those key on
//! `PathBuf` rather than on a URI and are not folded in here yet.

use dashmap::DashMap;
use tower_lsp::lsp_types::Url;

/// Raw URI spellings mapped to one canonical file identity.
#[derive(Debug, Default)]
pub(crate) struct DocumentUris {
    aliases: DashMap<String, String>,
}

impl DocumentUris {
    /// Record `uri`'s filesystem identity, resolving symlinks and the
    /// platform's spelling of the path. That touches the disk, so callers on
    /// the request path run it on the blocking pool. A URI that will not
    /// resolve — a file that does not exist yet, a non-file scheme — records
    /// nothing and keeps the syntactic key, which is still an improvement on
    /// the raw string.
    pub(crate) fn register(&self, uri: &str) {
        if self.aliases.contains_key(uri) {
            return;
        }
        let normalized = Self::normalized(uri);
        let Some(canonical) = Self::canonical(&normalized) else {
            return;
        };
        // Alias the raw spelling too, so the common case — the client sends a
        // byte-identical URI on every edit — resolves on a hash lookup rather
        // than re-parsing the URL.
        self.aliases.insert(uri.to_string(), canonical.clone());
        self.aliases.insert(normalized, canonical);
    }

    /// The key `uri` is indexed under: its filesystem identity if one has been
    /// resolved, otherwise its syntactic normalization. Parsing a URL folds
    /// `.` segments and percent-encoding, so spellings that differ only on
    /// paper agree even without a syscall — but the raw spelling is tried
    /// first, since this runs on the edit path and a registered document sends
    /// the same bytes every time.
    pub(crate) fn key(&self, uri: &str) -> String {
        if let Some(key) = self.aliases.get(uri) {
            return key.value().clone();
        }
        let normalized = Self::normalized(uri);
        self.aliases
            .get(&normalized)
            .map(|key| key.value().clone())
            .unwrap_or(normalized)
    }

    /// A URI's basename, for a message naming a file to the user. Falls back
    /// to the whole URI when it names no file.
    pub(crate) fn display_name(uri: &str) -> String {
        Url::parse(uri)
            .ok()
            .as_ref()
            .map(Self::display_name_of)
            .unwrap_or_else(|| uri.to_string())
    }

    /// [`Self::display_name`] for a URL the caller already holds.
    pub(crate) fn display_name_of(url: &Url) -> String {
        url.to_file_path()
            .ok()
            .as_deref()
            .and_then(std::path::Path::file_name)
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_else(|| url.to_string())
    }

    fn normalized(uri: &str) -> String {
        Url::parse(uri)
            .map(Into::into)
            .unwrap_or_else(|_| uri.to_string())
    }

    fn canonical(uri: &str) -> Option<String> {
        let path = Url::parse(uri).ok()?.to_file_path().ok()?;
        let canonical = std::fs::canonicalize(path).ok()?;
        Url::from_file_path(canonical).ok().map(Into::into)
    }
}

#[cfg(test)]
mod tests {
    use super::DocumentUris;

    #[test]
    fn an_unregistered_spelling_keys_as_itself() {
        let uris = DocumentUris::default();
        assert_eq!(uris.key("file:///m.eventb"), "file:///m.eventb");
    }

    #[test]
    fn dot_segments_agree_without_touching_the_disk() {
        // Neither file exists, so nothing can be canonicalized; parsing alone
        // has to fold the spellings together.
        let uris = DocumentUris::default();
        assert_eq!(
            uris.key("file:///dir/./m.eventb"),
            uris.key("file:///dir/m.eventb")
        );
    }

    #[test]
    fn spellings_of_one_file_share_a_key() {
        let root = crate::test_util::TempDir::new("eventb-lsp-uri-identity");
        let path = root.join("m.eventb");
        std::fs::write(&path, "CONTEXT c\nEND\n").unwrap();
        let direct = tower_lsp::lsp_types::Url::from_file_path(&path).unwrap();
        let indirect =
            tower_lsp::lsp_types::Url::from_file_path(root.join(".").join("m.eventb")).unwrap();

        let uris = DocumentUris::default();
        uris.register(direct.as_str());
        uris.register(indirect.as_str());

        assert_eq!(uris.key(direct.as_str()), uris.key(indirect.as_str()));
    }
}

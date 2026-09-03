//! A grammar fuzzer for the Rossi Event-B toolchain.
//!
//! The fuzzer derives Event-B text from the tree-sitter grammar
//! (`editors/tree-sitter-eventb/src/grammar.json`) and feeds it to Rossi's
//! parser, printer, XML writer and static checker, looking for crashes, hangs
//! and broken round trips. The tree-sitter grammar is the generation source
//! because it is a plain context-free grammar; Rossi's own pest grammar is a
//! PEG whose ordered choice and negative-lookahead guards make a derivation
//! mean something other than what it reads, so it serves as the oracle
//! instead.
//!
//! The grammar lives in a git submodule. Everything here degrades to a skip
//! when it is missing, so a clone without `--recurse-submodules` still builds
//! and tests — except where [`REQUIRE_GRAMMAR_ENV`] is set, which is our own
//! CI, and there a missing grammar is an error rather than a silently reduced
//! test run.

pub mod choice;
pub mod generate;
pub mod grammar;
pub mod regex;
pub mod vocab;

use std::path::{Path, PathBuf};

/// Environment variable naming the `grammar.json` to generate from, overriding
/// the copy in the submodule.
pub const GRAMMAR_ENV: &str = "EVENTB_TS_GRAMMAR";

/// The repository root, derived from this crate's manifest directory.
pub fn repository_root() -> PathBuf {
    let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    path.pop();
    path.pop();
    path
}

/// The path to the tree-sitter grammar, if it is present.
///
/// Honours [`GRAMMAR_ENV`] first so a caller can point the fuzzer at a
/// modified grammar (which is how grammar-mutation runs work) without moving
/// the submodule.
pub fn grammar_path() -> Option<PathBuf> {
    let path = match std::env::var_os(GRAMMAR_ENV) {
        // A relative override resolves from the repository root, matching how
        // the corpus harnesses read their own path variables.
        Some(value) => repository_root().join(value),
        None => repository_root().join("editors/tree-sitter-eventb/src/grammar.json"),
    };
    path.is_file().then_some(path)
}

/// Load the tree-sitter grammar from `path`.
///
/// A caller that has no path at all — [`grammar_path`] returned `None` —
/// decides between skipping and failing with [`grammar_is_required`], because
/// a CI run that silently tests nothing is worse than a failing one.
pub fn load_grammar_from(path: &Path) -> Result<grammar::Grammar, String> {
    let json =
        std::fs::read_to_string(path).map_err(|error| format!("{}: {error}", path.display()))?;
    grammar::Grammar::from_json(&json).map_err(|error| format!("{}: {error}", path.display()))
}

/// Load the tree-sitter grammar, deciding for the caller whether its absence
/// is a skip or a failure.
///
/// `Ok(None)` means "not there, and that is allowed" — the submodule is
/// missing in a plain clone. Where [`REQUIRE_GRAMMAR_ENV`] is set it is an
/// error instead, because a run that silently tests nothing is worse than one
/// that fails.
pub fn load_grammar() -> Result<Option<grammar::Grammar>, String> {
    match grammar_path() {
        Some(path) => load_grammar_from(&path).map(Some),
        None if grammar_is_required() => Err(MISSING_GRAMMAR.to_string()),
        None => Ok(None),
    }
}

/// The message explaining a missing grammar, for callers that skip.
pub const MISSING_GRAMMAR: &str =
    "tree-sitter grammar not found: run `git submodule update --init` or set EVENTB_TS_GRAMMAR";

/// Environment variable that turns a missing grammar from a skip into an
/// error. Set in this repository's own CI, where the submodule is always
/// checked out; deliberately not the generic `CI`, so that packagers building
/// the release tarball (which carries no submodule) inside their own CI get
/// the skip this crate documents rather than a failure.
pub const REQUIRE_GRAMMAR_ENV: &str = "EVENTB_FUZZ_REQUIRE_GRAMMAR";

/// Whether a missing grammar must be treated as an error.
pub fn grammar_is_required() -> bool {
    std::env::var_os(REQUIRE_GRAMMAR_ENV).is_some()
}

#[doc(hidden)]
pub mod test_support {
    use crate::grammar::Grammar;

    /// The grammar for tests, or `None` when the submodule is absent.
    ///
    /// Panics rather than skipping where [`crate::REQUIRE_GRAMMAR_ENV`] is
    /// set: see [`crate::grammar_is_required`].
    pub fn load_grammar() -> Option<Grammar> {
        match crate::load_grammar() {
            Ok(Some(grammar)) => Some(grammar),
            Ok(None) => {
                eprintln!("SKIP: {}", crate::MISSING_GRAMMAR);
                None
            }
            Err(error) => panic!("{error}"),
        }
    }
}

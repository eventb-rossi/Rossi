//! Canonical Event-B structural keywords.
//!
//! This module is the single source of truth for section keywords, event
//! keywords, status values, and the inline `theorem`/`skip` modifiers. It
//! mirrors [`crate::operators`]: a const table ([`KEYWORDS`]) plus lookup
//! helpers. LSP features (completion, hover, semantic tokens, folding) and the
//! parser's error recovery all derive their keyword sets from this table rather
//! than restating them.
//!
//! The vocabulary matches the structural keyword list documented in
//! `docs/EVENTB_LANGUAGE_REFERENCE.md` and is kept in sync with `grammar.pest`
//! by the `keywords_match_grammar` test.

/// Stable identifier for a structural keyword.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum KeywordId {
    // Component
    Context,
    Machine,
    End,
    // Context clauses
    Extends,
    Sets,
    Constants,
    Axioms,
    // Machine clauses
    Refines,
    Sees,
    Variables,
    Invariants,
    Variant,
    Events,
    // Event declarations
    Event,
    Initialisation,
    // Event clauses
    Status,
    Any,
    Where,
    With,
    Witness,
    Then,
    // Status values
    Ordinary,
    Convergent,
    Anticipated,
    // Inline modifiers (appear inside predicates/actions, not as clause headers)
    Theorem,
    Skip,
    // The THEOREMS section header (context and machine). The parser lowers its
    // members into the axioms/invariants vec with `is_theorem = true`, since Rodin
    // models a theorem as a flagged axiom/invariant, not a separate container.
    Theorems,
}

/// Structural grouping, used to derive context-specific keyword sets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KeywordGroup {
    Component,
    ContextClause,
    MachineClause,
    EventDecl,
    EventClause,
    Status,
    Inline,
}

/// Completion-context bitflags: the structural scopes where a keyword may be
/// offered as a completion.
pub mod scope {
    /// Outside any component (offers `CONTEXT`, `MACHINE`).
    pub const TOP_LEVEL: u8 = 1 << 4;
    /// Inside an `INITIALISATION` event before its action clause.
    pub const INITIALISATION: u8 = 1 << 5;
    /// After an event's terminal action clause (offers only `END`).
    pub const EVENT_END: u8 = 1 << 6;
    pub const CONTEXT: u8 = 1 << 0;
    pub const MACHINE: u8 = 1 << 1;
    /// The `EVENTS` section body (offers `EVENT`, `INITIALISATION`).
    pub const EVENTS: u8 = 1 << 2;
    /// Inside a single event.
    pub const EVENT: u8 = 1 << 3;
}

/// A structural keyword and its associated metadata.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Keyword {
    pub id: KeywordId,
    /// Accepted spellings, canonical (display) form first
    /// (e.g. `["WHERE", "WHEN"]`). Section/event keywords are uppercase, status
    /// and inline keywords lowercase; all lookups are case-insensitive.
    pub spellings: &'static [&'static str],
    pub group: KeywordGroup,
    /// Bitmask of [`scope`] flags where this keyword is offered in completion;
    /// `0` means it is never offered as a context keyword.
    pub completion_scopes: u8,
    /// Short description shown in completion items.
    pub summary: &'static str,
}

impl Keyword {
    /// Canonical (display) spelling.
    pub const fn text(&self) -> &'static str {
        self.spellings[0]
    }
}

const fn kw(
    id: KeywordId,
    spellings: &'static [&'static str],
    group: KeywordGroup,
    completion_scopes: u8,
    summary: &'static str,
) -> Keyword {
    Keyword {
        id,
        spellings,
        group,
        completion_scopes,
        summary,
    }
}

use KeywordGroup as Grp;
use KeywordId::*;

pub const KEYWORDS: &[Keyword] = &[
    // Component
    kw(
        Context,
        &["CONTEXT"],
        Grp::Component,
        scope::TOP_LEVEL,
        "Define a context (static properties)",
    ),
    kw(
        Machine,
        &["MACHINE"],
        Grp::Component,
        scope::TOP_LEVEL,
        "Define a machine (dynamic behavior)",
    ),
    kw(
        End,
        &["END"],
        Grp::Component,
        scope::CONTEXT | scope::MACHINE | scope::EVENT | scope::INITIALISATION | scope::EVENT_END,
        "End the current block",
    ),
    // Context clauses
    kw(
        Extends,
        &["EXTENDS"],
        Grp::ContextClause,
        scope::CONTEXT | scope::EVENT | scope::INITIALISATION,
        "Extend another context or abstract event",
    ),
    kw(
        Sets,
        &["SETS"],
        Grp::ContextClause,
        scope::CONTEXT,
        "Define carrier sets",
    ),
    kw(
        Constants,
        &["CONSTANTS"],
        Grp::ContextClause,
        scope::CONTEXT,
        "Define constants",
    ),
    kw(
        Axioms,
        &["AXIOMS"],
        Grp::ContextClause,
        scope::CONTEXT,
        "Define axioms (properties)",
    ),
    // Machine clauses
    kw(
        Refines,
        &["REFINES"],
        Grp::MachineClause,
        scope::MACHINE | scope::EVENT,
        "Refine an abstract machine or event",
    ),
    kw(
        Sees,
        &["SEES"],
        Grp::MachineClause,
        scope::MACHINE,
        "See a context",
    ),
    kw(
        Variables,
        &["VARIABLES"],
        Grp::MachineClause,
        scope::MACHINE,
        "Define state variables",
    ),
    kw(
        Invariants,
        &["INVARIANTS"],
        Grp::MachineClause,
        scope::MACHINE,
        "Define invariants (properties)",
    ),
    kw(
        Variant,
        &["VARIANT"],
        Grp::MachineClause,
        scope::MACHINE,
        "Define variant for termination",
    ),
    kw(
        Events,
        &["EVENTS"],
        Grp::MachineClause,
        scope::MACHINE,
        "Begin events section",
    ),
    // Event declarations
    kw(
        Event,
        &["EVENT"],
        Grp::EventDecl,
        scope::EVENTS,
        "Define a new event",
    ),
    kw(
        Initialisation,
        &["INITIALISATION"],
        Grp::EventDecl,
        scope::EVENTS,
        "Define initialization event",
    ),
    // Event clauses
    kw(
        Status,
        &["STATUS"],
        Grp::EventClause,
        scope::EVENT,
        "Define event status",
    ),
    kw(
        Any,
        &["ANY"],
        Grp::EventClause,
        scope::EVENT,
        "Introduce event parameters",
    ),
    kw(
        Where,
        &["WHERE", "WHEN"],
        Grp::EventClause,
        scope::EVENT,
        "Define event guards",
    ),
    kw(
        With,
        &["WITH"],
        Grp::EventClause,
        scope::EVENT,
        "Specify witnesses",
    ),
    kw(
        Witness,
        &["WITNESS"],
        Grp::EventClause,
        scope::EVENT,
        "Define witness values",
    ),
    kw(
        Then,
        &["THEN", "BEGIN"],
        Grp::EventClause,
        scope::EVENT | scope::INITIALISATION,
        "Define event actions",
    ),
    // Status values (offered via a `STATUS`-line trigger, not a block scope)
    kw(
        Ordinary,
        &["ordinary"],
        Grp::Status,
        0,
        "Ordinary event (default)",
    ),
    kw(
        Convergent,
        &["convergent"],
        Grp::Status,
        0,
        "Convergent event (decreases variant)",
    ),
    kw(
        Anticipated,
        &["anticipated"],
        Grp::Status,
        0,
        "Anticipated event (may increase variant)",
    ),
    // Inline modifiers
    kw(
        Theorem,
        &["theorem"],
        Grp::Inline,
        0,
        "Mark a labeled predicate as a theorem",
    ),
    kw(
        Skip,
        &["skip"],
        Grp::Inline,
        0,
        "No-op action (does nothing)",
    ),
    // A context AND machine clause; the dual scope is carried by `completion_scopes`
    // (mirroring EXTENDS/REFINES). Members lower into the axioms/invariants vec with
    // `is_theorem = true` — a theorem is a flagged axiom/invariant in Rodin's model.
    kw(
        Theorems,
        &["THEOREMS"],
        Grp::ContextClause,
        scope::CONTEXT | scope::MACHINE,
        "Declares theorems (properties proved once, not preserved by events)",
    ),
];

/// Look up a keyword by any of its spellings (case-insensitive).
pub fn lookup(word: &str) -> Option<&'static Keyword> {
    KEYWORDS
        .iter()
        .find(|k| k.spellings.iter().any(|s| s.eq_ignore_ascii_case(word)))
}

/// The keyword for an id. Panics if the table is missing it (mirrors
/// [`crate::operators::spelling`]).
pub fn keyword(id: KeywordId) -> &'static Keyword {
    KEYWORDS
        .iter()
        .find(|k| k.id == id)
        .expect("keyword is missing from KEYWORDS")
}

/// Canonical spelling for an id.
pub fn spell(id: KeywordId) -> &'static str {
    keyword(id).text()
}

/// Whether `word` is any structural keyword (case-insensitive).
pub fn is_keyword(word: &str) -> bool {
    lookup(word).is_some()
}

/// Where a declared name is written back in `.eventb` text. The grammar
/// guards each name list only against its own section's follow-set
/// (`context_section_kw`, `machine_section_kw`, `event_section_kw` and
/// `event_refines_follow_kw` in `grammar.pest`), so which keywords re-lex a
/// name depends on the site.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclSite {
    /// A context name: listed under `EXTENDS` and `SEES`.
    ContextName,
    /// A machine name: only ever the sole `REFINES` target, which the grammar
    /// never guards, so it collides with nothing here (only with Camille's
    /// tokens, see [`camille_reserved_keyword`]).
    MachineName,
    /// A carrier set or constant: listed under `SETS` / `CONSTANTS`.
    ContextItem,
    /// A variable: listed under `VARIABLES`.
    Variable,
    /// An event name: listed as an event's `REFINES` target; also
    /// `INITIALISATION`, which the event header captures as the init event.
    EventName,
    /// An event parameter: listed under `ANY`.
    Parameter,
}

// The inline keywords re-lex a name wherever it is *used*: `theorem` in any
// labeled predicate, so every identifier site collides with it; `skip` only
// as an action's target, so only variables do (`x ≔ skip + 1` parses).
const INLINE: &[KeywordId] = &[Theorem];
const INLINE_VARIABLE: &[KeywordId] = &[Theorem, Skip];
const CONTEXT_SECTION: &[KeywordId] = &[Extends, Sets, Constants, Axioms, Theorems, End];
const MACHINE_SECTION: &[KeywordId] = &[
    Refines, Sees, Variables, Invariants, Theorems, Variant, Events, End,
];
const EVENT_SECTION: &[KeywordId] = &[Where, With, Witness, Then, End];
const EVENT_REFINES_FOLLOW: &[KeywordId] = &[Status, Any];
// Not a follow-set: the event header's ordered choice
// (`initialisation_event | event`) captures a name spelled this way as the
// INITIALISATION event.
const EVENT_HEADER: &[KeywordId] = &[Initialisation];

/// The spelling of the structural keyword rossi's own grammar takes a
/// declared name spelled `word` for when written at `site`, if any
/// (case-insensitive, like the tokens; an alias such as `begin` reports
/// `BEGIN`, not `THEN`). Only the keywords that terminate the site's list
/// (or, for identifiers, re-lex a use) collide: a variable named `status`
/// survives every rossi round trip and is not reported here. Stock Camille's
/// stricter lexicon is [`camille_reserved_keyword`].
pub fn colliding_keyword(word: &str, site: DeclSite) -> Option<&'static str> {
    let sets: &[&[KeywordId]] = match site {
        DeclSite::ContextName => &[CONTEXT_SECTION, MACHINE_SECTION],
        DeclSite::MachineName => &[],
        DeclSite::ContextItem => &[CONTEXT_SECTION, INLINE],
        DeclSite::Variable => &[MACHINE_SECTION, INLINE_VARIABLE],
        DeclSite::EventName => &[EVENT_SECTION, EVENT_REFINES_FOLLOW, EVENT_HEADER],
        DeclSite::Parameter => &[EVENT_SECTION, INLINE],
    };
    spelling_among(word, sets)
}

/// The spelling of `word` in the table, if it is (case-insensitively) a
/// spelling of a keyword in one of `sets`.
fn spelling_among(word: &str, sets: &[&[KeywordId]]) -> Option<&'static str> {
    lookup(word)
        .filter(|k| sets.iter().any(|s| s.contains(&k.id)))?
        .spellings
        .iter()
        .copied()
        .find(|s| s.eq_ignore_ascii_case(word))
}

// Stock Camille (Rodin's text editor, `EventBParser.scc`) lexes these as
// tokens in their lowercase spelling only, ahead of `identifier_literal`; it
// has no `INITIALISATION`, `STATUS`, `WITNESS`, `skip` or `THEOREMS` tokens.
const CAMILLE: &[KeywordId] = &[
    Context,
    Machine,
    End,
    Extends,
    Sets,
    Constants,
    Axioms,
    Refines,
    Sees,
    Variables,
    Invariants,
    Variant,
    Events,
    Event,
    Any,
    Where,
    With,
    Then,
    Ordinary,
    Convergent,
    Anticipated,
    Theorem,
];

/// The spelling of the structural keyword stock Camille lexes a declared
/// name spelled `word` as, wherever it is written, if any. Camille's tokens
/// are lowercase and case-sensitive, so only an all-lowercase `word`
/// collides: `machine` cannot be read as a name anywhere in a Camille file,
/// `Machine` can.
pub fn camille_reserved_keyword(word: &str) -> Option<&'static str> {
    if word.bytes().any(|b| b.is_ascii_uppercase()) {
        return None;
    }
    spelling_among(word, &[CAMILLE])
}

/// Keywords offered in the given completion scope (a bitmask of [`scope`] flags).
pub fn iter_completion_scope(scope_mask: u8) -> impl Iterator<Item = &'static Keyword> {
    KEYWORDS
        .iter()
        .filter(move |k| k.completion_scopes & scope_mask != 0)
}

/// Keywords in the given group.
pub fn iter_group(group: KeywordGroup) -> impl Iterator<Item = &'static Keyword> {
    KEYWORDS.iter().filter(move |k| k.group == group)
}

/// A context or machine clause header (the folding/clause boundary group).
fn is_clause_group(k: &Keyword) -> bool {
    matches!(k.group, Grp::ContextClause | Grp::MachineClause)
}

/// A clause header or `END` (the parser's error-recovery boundary set).
fn is_recovery_group(k: &Keyword) -> bool {
    is_clause_group(k) || k.id == End
}

/// Whether `word` begins a context/machine clause (used by folding boundaries).
pub fn is_clause_keyword(word: &str) -> bool {
    lookup(word).is_some_and(is_clause_group)
}

/// Whether `word` begins a clause or ends a component (used by the parser's
/// error-recovery clause splitting). Equivalent to [`is_clause_keyword`] plus `END`.
pub fn is_recovery_boundary(word: &str) -> bool {
    lookup(word).is_some_and(is_recovery_group)
}

/// Whether `word` starts any structural region (used by clause-boundary
/// detection). Every keyword except the status values and inline modifiers.
pub fn is_clause_boundary(word: &str) -> bool {
    lookup(word).is_some_and(|k| !matches!(k.group, Grp::Status | Grp::Inline))
}

/// Whether `c` continues a word for keyword-boundary purposes: a keyword
/// match counts as whole-word only when neither neighbour is one of these.
/// Mirrors the grammar's `word_char` (the body of `word_boundary`): ASCII
/// alphanumerics and `_`. A trailing identifier prime `'` is deliberately
/// excluded — as in the grammar (and Event-B), a prime attaches only to a
/// plain identifier, so a keyword followed by `'` is still that keyword
/// (`mod'` is `mod` then `'`). Math contexts keep recognizing words across
/// `-` (`a-dom(r)` lexes `dom` as an operator); structural scans use
/// [`is_structural_word_char`] instead.
pub fn is_word_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_'
}

/// [`is_word_char`] plus `-`, mirroring the grammar's `struct_word_boundary`:
/// a hyphen-joined `component_name` like `end-to-end` or `the-MACHINE-x` must
/// never be split at an embedded keyword.
pub fn is_structural_word_char(c: char) -> bool {
    is_word_char(c) || c == '-'
}

/// Whether the match of `len` bytes at byte `offset` in `text` is a whole
/// word: neither neighboring char is a word char. Shared by the recovery
/// parser's keyword scan and the LSP's semantic-token search so the two
/// can never disagree on word boundaries.
pub fn is_word_bounded(text: &str, offset: usize, len: usize) -> bool {
    word_bounded_by(text, offset, len, is_word_char)
}

/// [`is_word_bounded`] under the structural-keyword boundary rule
/// ([`is_structural_word_char`]). Used by the recovery parser when scanning
/// for structural keywords (component headers, clause boundaries).
pub fn is_structural_word_bounded(text: &str, offset: usize, len: usize) -> bool {
    word_bounded_by(text, offset, len, is_structural_word_char)
}

/// The whole-word boundary rule appropriate for a `name` needle: a hyphenated
/// needle can only be a component name, so it takes the structural boundary
/// (where `-` is part of the word); a hyphen-free needle is a math identifier,
/// where `-` is the subtraction operator, so it keeps the math boundary. The
/// `rossi` analogue of the LSP's `WordBoundary::for_name`.
pub fn word_bounded_for_name(name: &str) -> fn(&str, usize, usize) -> bool {
    if name.contains('-') {
        is_structural_word_bounded
    } else {
        is_word_bounded
    }
}

fn word_bounded_by(text: &str, offset: usize, len: usize, is_part: fn(char) -> bool) -> bool {
    let before_ok = !text[..offset].chars().next_back().is_some_and(is_part);
    let after_ok = !text[offset + len..].chars().next().is_some_and(is_part);
    before_ok && after_ok
}

/// Uppercase spellings of all recovery-boundary keywords, for the parser's
/// offset scan over an uppercased component body.
pub fn recovery_boundary_spellings() -> impl Iterator<Item = &'static str> {
    KEYWORDS
        .iter()
        .filter(|&k| is_recovery_group(k))
        .flat_map(|k| k.spellings.iter().copied())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn all_ids() -> [KeywordId; 27] {
        [
            Context,
            Machine,
            End,
            Extends,
            Sets,
            Constants,
            Axioms,
            Refines,
            Sees,
            Variables,
            Invariants,
            Variant,
            Events,
            Event,
            Initialisation,
            Status,
            Any,
            Where,
            With,
            Witness,
            Then,
            Ordinary,
            Convergent,
            Anticipated,
            Theorem,
            Skip,
            Theorems,
        ]
    }

    #[test]
    fn every_id_has_exactly_one_row() {
        for id in all_ids() {
            let rows = KEYWORDS.iter().filter(|k| k.id == id).count();
            assert_eq!(rows, 1, "{id:?} should have exactly one row, found {rows}");
        }
        assert_eq!(
            KEYWORDS.len(),
            all_ids().len(),
            "KEYWORDS has rows not covered by all_ids()"
        );
    }

    #[test]
    fn lookup_round_trips_every_id() {
        for id in all_ids() {
            assert_eq!(lookup(keyword(id).text()).map(|k| k.id), Some(id));
        }
    }

    #[test]
    fn lookup_is_case_insensitive() {
        let a = lookup("SETS").map(|k| k.id);
        assert_eq!(a, Some(Sets));
        assert_eq!(lookup("sets").map(|k| k.id), a);
        assert_eq!(lookup("Sets").map(|k| k.id), a);
    }

    #[test]
    fn aliases_resolve_to_canonical_id() {
        assert_eq!(lookup("WHEN").map(|k| k.id), Some(Where));
        assert_eq!(lookup("BEGIN").map(|k| k.id), Some(Then));
        assert_eq!(spell(Where), "WHERE");
        assert_eq!(spell(Then), "THEN");
    }

    #[test]
    fn colliding_keyword_follows_the_site_terminators() {
        use DeclSite::*;
        // `END` terminates every list; the rest depend on the site.
        for site in [ContextName, ContextItem, Variable, EventName, Parameter] {
            for s in ["end", "End", "END"] {
                assert_eq!(colliding_keyword(s, site), Some("END"), "{site:?}");
            }
            assert!(colliding_keyword("price", site).is_none());
            // Header/status words never end a name list.
            assert!(colliding_keyword("machine", site).is_none(), "{site:?}");
            assert!(colliding_keyword("ordinary", site).is_none(), "{site:?}");
        }
        // A machine name is only ever the sole REFINES target: unguarded.
        assert!(colliding_keyword("end", MachineName).is_none());
        assert_eq!(colliding_keyword("Sets", ContextItem), Some("SETS"));
        assert!(colliding_keyword("sets", Variable).is_none());
        assert_eq!(colliding_keyword("variables", Variable), Some("VARIABLES"));
        assert!(colliding_keyword("variables", Parameter).is_none());
        assert_eq!(colliding_keyword("Begin", Parameter), Some("BEGIN"));
        assert_eq!(colliding_keyword("when", EventName), Some("WHEN"));
        // A context name is listed under both EXTENDS and SEES.
        assert_eq!(colliding_keyword("sees", ContextName), Some("SEES"));
        assert_eq!(colliding_keyword("axioms", ContextName), Some("AXIOMS"));
        // STATUS / INITIALISATION break only in the event header.
        assert_eq!(colliding_keyword("status", EventName), Some("STATUS"));
        assert_eq!(
            colliding_keyword("Initialisation", EventName),
            Some("INITIALISATION")
        );
        assert!(colliding_keyword("status", Variable).is_none());
        // Inline keywords re-lex any *use*, so identifiers collide anywhere.
        assert_eq!(colliding_keyword("skip", Variable), Some("skip"));
        assert!(colliding_keyword("skip", ContextItem).is_none());
        assert!(colliding_keyword("skip", Parameter).is_none());
        assert_eq!(colliding_keyword("theorem", ContextItem), Some("theorem"));
        assert!(colliding_keyword("skip", EventName).is_none());
    }

    #[test]
    fn site_terminators_match_grammar() {
        // The per-site terminator sets mirror the grammar's follow-set rules
        // (`x = _{ kw_a | kw_b | ... }`, one per line); a keyword added to or
        // dropped from one of those rules must be mirrored here, or EB028
        // drifts from what the parser actually re-lexes.
        let grammar = include_str!("grammar.pest");
        let rule_words = |rule: &str| -> HashSet<String> {
            let line = grammar
                .lines()
                .find(|l| l.starts_with(&format!("{rule} =")))
                .unwrap_or_else(|| panic!("{rule} missing from grammar.pest"));
            line.split_whitespace()
                .filter_map(|w| w.strip_prefix("kw_"))
                .map(str::to_string)
                .collect()
        };
        let table_words = |ids: &[KeywordId]| -> HashSet<String> {
            ids.iter()
                .flat_map(|id| keyword(*id).spellings.iter())
                .map(|s| s.to_ascii_lowercase())
                .collect()
        };
        assert_eq!(
            rule_words("context_section_kw"),
            table_words(CONTEXT_SECTION)
        );
        assert_eq!(
            rule_words("machine_section_kw"),
            table_words(MACHINE_SECTION)
        );
        assert_eq!(rule_words("event_section_kw"), table_words(EVENT_SECTION));
        // `event_refines_follow_kw` also names `event_section_kw` (checked
        // above), which the scraper skips as it carries no `kw_` prefix.
        assert_eq!(
            rule_words("event_refines_follow_kw"),
            table_words(EVENT_REFINES_FOLLOW)
        );
    }

    #[test]
    fn camille_reserved_keyword_is_lowercase_only() {
        // EventBParser.scc (probparsers/eventbstruct): the structural tokens,
        // all lowercase; `where`/`when` and `then`/`begin` share a token.
        let expected: HashSet<&str> = HashSet::from([
            "ordinary",
            "convergent",
            "anticipated",
            "machine",
            "refines",
            "sees",
            "variables",
            "invariants",
            "theorem",
            "events",
            "variant",
            "end",
            "context",
            "extends",
            "sets",
            "constants",
            "axioms",
            "event",
            "any",
            "where",
            "when",
            "with",
            "then",
            "begin",
        ]);
        for w in &expected {
            assert_eq!(
                camille_reserved_keyword(w).map(str::to_ascii_lowercase),
                Some(w.to_string())
            );
        }
        for k in KEYWORDS {
            for s in k.spellings {
                let lower = s.to_ascii_lowercase();
                assert_eq!(
                    camille_reserved_keyword(&lower).is_some(),
                    expected.contains(lower.as_str()),
                    "{lower}"
                );
                // Camille's tokens are case-sensitive: any other case is a name.
                assert!(
                    camille_reserved_keyword(&s.to_ascii_uppercase()).is_none(),
                    "{s}"
                );
            }
        }
        assert_eq!(camille_reserved_keyword("machine"), Some("MACHINE"));
        assert_eq!(camille_reserved_keyword("begin"), Some("BEGIN"));
        assert!(camille_reserved_keyword("Machine").is_none());
    }

    #[test]
    fn dual_scope_and_status_scopes() {
        assert_eq!(keyword(Context).completion_scopes, scope::TOP_LEVEL);
        assert_eq!(keyword(Machine).completion_scopes, scope::TOP_LEVEL);
        assert_eq!(
            keyword(End).completion_scopes & scope::EVENT_END,
            scope::EVENT_END
        );
        assert_eq!(
            keyword(Then).completion_scopes & scope::INITIALISATION,
            scope::INITIALISATION
        );
        assert_eq!(
            keyword(Refines).completion_scopes,
            scope::MACHINE | scope::EVENT
        );
        assert_eq!(
            keyword(Extends).completion_scopes,
            scope::CONTEXT | scope::EVENT | scope::INITIALISATION
        );
        for k in iter_group(KeywordGroup::Status) {
            assert_eq!(
                k.completion_scopes, 0,
                "{:?} should not be a context keyword",
                k.id
            );
        }
    }

    #[test]
    fn boundary_predicates_are_nested_subsets() {
        let clause: HashSet<&str> = KEYWORDS
            .iter()
            .flat_map(|k| k.spellings.iter().copied())
            .filter(|w| is_clause_keyword(w))
            .collect();
        let recovery: HashSet<&str> = KEYWORDS
            .iter()
            .flat_map(|k| k.spellings.iter().copied())
            .filter(|w| is_recovery_boundary(w))
            .collect();
        let boundary: HashSet<&str> = KEYWORDS
            .iter()
            .flat_map(|k| k.spellings.iter().copied())
            .filter(|w| is_clause_boundary(w))
            .collect();

        assert!(clause.is_subset(&recovery));
        assert!(recovery.is_subset(&boundary));
        let extra: HashSet<&str> = recovery.difference(&clause).copied().collect();
        assert_eq!(extra, HashSet::from(["END"]));
    }

    #[test]
    fn theorems_is_a_clause_keyword() {
        // THEOREMS is a real context+machine clause: it folds, bounds recovery, and
        // is offered for completion in both component scopes.
        assert!(is_clause_keyword("THEOREMS"));
        assert!(is_recovery_boundary("THEOREMS"));
        assert!(is_clause_boundary("THEOREMS"));
        assert_eq!(
            keyword(Theorems).completion_scopes,
            scope::CONTEXT | scope::MACHINE
        );
        assert!(iter_completion_scope(scope::CONTEXT).any(|k| k.id == Theorems));
        assert!(iter_completion_scope(scope::MACHINE).any(|k| k.id == Theorems));
    }

    #[test]
    fn keywords_match_grammar() {
        let grammar = include_str!("grammar.pest");
        // Collect every `kw_xxx = @{ ^"xxx" ... }` literal, lowercased.
        let mut grammar_kw: HashSet<String> = HashSet::new();
        for line in grammar.lines() {
            let line = line.trim_start();
            if !line.starts_with("kw_") {
                continue;
            }
            if let Some(start) = line.find("^\"") {
                let rest = &line[start + 2..];
                if let Some(end) = rest.find('"') {
                    grammar_kw.insert(rest[..end].to_ascii_lowercase());
                }
            }
        }

        // Forward: every table spelling has a `kw_` rule in the grammar.
        for k in KEYWORDS {
            for s in k.spellings {
                assert!(
                    grammar_kw.contains(&s.to_ascii_lowercase()),
                    "table spelling {s:?} has no kw_ rule in grammar.pest"
                );
            }
        }

        // Reverse: every grammar keyword is in the table, except the
        // math-language keywords handled by `builtins`/`operators`.
        let allow = [
            "true", "false", "nat", "nat1", "int", "bool", "if", "else", "union", "inter",
        ];
        let table: HashSet<String> = KEYWORDS
            .iter()
            .flat_map(|k| k.spellings.iter().map(|s| s.to_ascii_lowercase()))
            .collect();
        for g in &grammar_kw {
            if allow.contains(&g.as_str()) {
                continue;
            }
            assert!(
                table.contains(g),
                "grammar keyword {g:?} is missing from KEYWORDS"
            );
        }
    }

    #[test]
    fn keywords_match_language_reference() {
        // docs/EVENTB_LANGUAGE_REFERENCE.md:352 — documented structural keyword list.
        // Two keywords are added here as known doc-omissions that the grammar and
        // EBNF nonetheless define: `STATUS` (event EBNF at :413) and `THEOREMS`
        // (context/machine EBNF at :391/:403 — the :352 list mentions only the
        // inline `theorem` flag).
        let expected = HashSet::from([
            "CONTEXT",
            "MACHINE",
            "EXTENDS",
            "REFINES",
            "SEES",
            "SETS",
            "CONSTANTS",
            "AXIOMS",
            "VARIABLES",
            "INVARIANTS",
            "VARIANT",
            "EVENTS",
            "EVENT",
            "ANY",
            "WHERE",
            "WHEN",
            "WITH",
            "WITNESS",
            "THEN",
            "BEGIN",
            "END",
            "INITIALISATION",
            "theorem",
            "ordinary",
            "convergent",
            "anticipated",
            "skip",
            "STATUS",
            "THEOREMS",
        ]);
        let table: HashSet<&str> = KEYWORDS
            .iter()
            .flat_map(|k| k.spellings.iter().copied())
            .collect();
        assert_eq!(table, expected);
    }
}

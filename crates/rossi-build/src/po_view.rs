//! A normalized, comparison-friendly view of a `.bpo` file.
//!
//! Like [`crate::sc_view`] for checked files, this re-parses a
//! proof-obligation file into a form where two generators' output can
//! be compared semantically:
//!
//! - predicate attributes are re-parsed into ASTs with type
//!   ascriptions stripped, so canonical and bare spellings compare
//!   equal;
//! - `source` and hint handles drop their leading `/PROJECT/` segment,
//!   so archives regenerated under a different project name still
//!   compare;
//! - the predicate-set chain is resolvable: a sequent's hypotheses can
//!   be flattened root-first through the `parentSet` links, making the
//!   comparison independent of which cut points were materialized.
//!
//! Stamps are parsed (so a regeneration can carry them forward from
//! previous output) but excluded from every comparison — they encode
//! edit history, not content.

use std::collections::{BTreeMap, BTreeSet};

use quick_xml::Reader;
use quick_xml::events::{BytesStart, Event};

use rossi::{Predicate, parse_predicate_str};

use crate::error::{ProjectError, Result};
use crate::handles::handle_segments;
use crate::sc_view::{string_attr, strip_type_ascriptions_pred};

/// One predicate row: the re-parsed formula plus its normalized source.
#[derive(Debug, Clone, PartialEq)]
pub struct PoPredicate {
    pub predicate: Predicate,
    pub source: Option<String>,
}

/// One top-level predicate set.
#[derive(Debug, Default)]
pub struct PoSet {
    /// The parent set's name, from the `parentSet` handle.
    pub parent: Option<String>,
    /// Typed identifiers, name → type string.
    pub identifiers: BTreeMap<String, String>,
    /// Predicate rows, in document order.
    pub predicates: Vec<PoPredicate>,
    /// The rows' internal names, parallel to `predicates` — the
    /// targets of predicate selection hints.
    pub predicate_names: Vec<String>,
    /// The set's `poStamp` attribute, verbatim.
    pub stamp: Option<String>,
}

/// A prover hint, with normalized handles.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PoHint {
    Interval { start: String, end: String },
    Predicate(String),
}

/// One proof obligation.
#[derive(Debug, Default)]
pub struct PoSequent {
    pub description: String,
    pub accurate: bool,
    /// The name of the set the sequent's local hypothesis set chains
    /// onto.
    pub parent_set: Option<String>,
    pub local_hypotheses: Vec<PoPredicate>,
    pub goal: Option<PoPredicate>,
    /// `(role, source)` rows, in document order.
    pub sources: Vec<(String, Option<String>)>,
    pub hints: Vec<PoHint>,
    /// The sequent's `poStamp` attribute, verbatim.
    pub stamp: Option<String>,
}

/// The parsed view of one `.bpo` file.
#[derive(Debug, Default)]
pub struct PoView {
    pub sets: BTreeMap<String, PoSet>,
    pub sequents: BTreeMap<String, PoSequent>,
    /// The root element's file-level `poStamp` attribute, verbatim.
    pub stamp: Option<String>,
}

impl PoView {
    /// Parse a `.bpo` document.
    pub fn from_xml(xml: &str) -> Result<PoView> {
        let mut reader = Reader::from_str(xml);
        let mut buf = Vec::new();
        let mut view = PoView::default();
        let mut scope = Scope::None;
        let mut depth = 0usize;

        loop {
            match reader.read_event_into(&mut buf) {
                Ok(Event::Start(e)) => {
                    handle_element(&mut view, &mut scope, depth, &e)?;
                    depth += 1;
                }
                Ok(Event::Empty(e)) => {
                    handle_element(&mut view, &mut scope, depth, &e)?;
                }
                Ok(Event::End(_)) => {
                    depth = depth.saturating_sub(1);
                    if depth <= 1 {
                        scope = Scope::None;
                    }
                }
                Ok(Event::Eof) => break,
                Err(e) => {
                    return Err(ProjectError::Xml(e).into());
                }
                _ => {}
            }
            buf.clear();
        }
        Ok(view)
    }

    /// The sequent's hypotheses flattened root-first through the
    /// predicate-set chain, then its local hypotheses.
    pub fn flattened_hypotheses(&self, sequent_name: &str) -> Vec<&PoPredicate> {
        let Some(sequent) = self.sequents.get(sequent_name) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for set_name in self.chain_root_first(sequent.parent_set.as_deref()) {
            if let Some(set) = self.sets.get(set_name) {
                out.extend(set.predicates.iter());
            }
        }
        out.extend(sequent.local_hypotheses.iter());
        out
    }

    /// The typed identifiers visible to the sequent, flattened through
    /// the predicate-set chain.
    pub fn flattened_identifiers(&self, sequent_name: &str) -> BTreeMap<&str, &str> {
        let Some(sequent) = self.sequents.get(sequent_name) else {
            return BTreeMap::new();
        };
        let mut out = BTreeMap::new();
        for set_name in self.chain_root_first(sequent.parent_set.as_deref()) {
            if let Some(set) = self.sets.get(set_name) {
                for (name, ty) in &set.identifiers {
                    out.insert(name.as_str(), ty.as_str());
                }
            }
        }
        out
    }

    /// The sequent's hints resolved to the content they select, so the
    /// comparison is independent of set naming: an interval hint
    /// becomes the predicates of the chain from its end up to
    /// (excluding) its start; a predicate hint becomes the row it
    /// points at.
    pub fn resolved_hints<'a>(&'a self, sequent_name: &str) -> Vec<ResolvedHint<'a>> {
        let Some(sequent) = self.sequents.get(sequent_name) else {
            return Vec::new();
        };
        sequent
            .hints
            .iter()
            .map(|hint| match hint {
                PoHint::Interval { start, end } => {
                    ResolvedHint::Interval(self.interval_selection(sequent, start, end))
                }
                PoHint::Predicate(target) => ResolvedHint::Predicate(self.predicate_target(target)),
            })
            .collect()
    }

    /// The predicates an interval hint selects, or `None` when the
    /// start set does not lie on the end set's chain — a dangling
    /// handle must stay distinguishable from a whole-chain selection,
    /// or hint regressions compare equal to correct output.
    fn interval_selection<'a>(
        &'a self,
        sequent: &'a PoSequent,
        start: &str,
        end: &str,
    ) -> Option<Vec<&'a PoPredicate>> {
        let start_set = handle_segments(start)
            .into_iter()
            .find(|(ty, _)| ty == "org.eventb.core.poPredicateSet")
            .map(|(_, name)| name);
        let segments = handle_segments(end);
        let end_is_seqhyp = segments
            .iter()
            .any(|(ty, _)| ty == "org.eventb.core.poSequent");
        let end_set = if end_is_seqhyp {
            sequent.parent_set.clone()
        } else {
            segments
                .into_iter()
                .find(|(ty, _)| ty == "org.eventb.core.poPredicateSet")
                .map(|(_, name)| name)
        };

        let chain = self.chain_root_first(end_set.as_deref());
        let cut = match start_set.as_deref() {
            Some(start) => chain.iter().position(|name| *name == start)? + 1,
            None => 0,
        };
        let mut out = Vec::new();
        for set_name in &chain[cut..] {
            if let Some(set) = self.sets.get(*set_name) {
                out.extend(set.predicates.iter());
            }
        }
        if end_is_seqhyp {
            out.extend(sequent.local_hypotheses.iter());
        }
        Some(out)
    }

    /// The row a predicate hint points at.
    fn predicate_target(&self, target: &str) -> Option<&PoPredicate> {
        let segments = handle_segments(target);
        let set_name = segments
            .iter()
            .find(|(ty, _)| ty == "org.eventb.core.poPredicateSet")
            .map(|(_, name)| name)?;
        let predicate_name = segments
            .iter()
            .find(|(ty, _)| ty == "org.eventb.core.poPredicate")
            .map(|(_, name)| name)?;
        let set = self.sets.get(set_name)?;
        let position = set
            .predicate_names
            .iter()
            .position(|name| name == predicate_name)?;
        set.predicates.get(position)
    }

    /// Whether the sequent named `name` is semantically unchanged
    /// between `self` and `other`: same nature, accuracy, goal,
    /// flattened hypothesis chain, visible identifiers, sources (as
    /// sets), and resolved hints. The field set mirrors the corpus
    /// gates' `diff_po_views` helper, which keeps its own copy for
    /// per-field diagnostics.
    pub fn sequent_eq(&self, other: &PoView, name: &str) -> bool {
        let (Some(mine), Some(theirs)) = (self.sequents.get(name), other.sequents.get(name)) else {
            return false;
        };
        let my_sources: BTreeSet<_> = mine.sources.iter().collect();
        let their_sources: BTreeSet<_> = theirs.sources.iter().collect();
        mine.description == theirs.description
            && mine.accurate == theirs.accurate
            && mine.goal == theirs.goal
            && self.flattened_hypotheses(name) == other.flattened_hypotheses(name)
            && self.flattened_identifiers(name) == other.flattened_identifiers(name)
            && my_sources == their_sources
            && self.resolved_hints(name) == other.resolved_hints(name)
    }

    /// Whether the top-level predicate set named `name` carries the
    /// same content in both views, including everything inherited
    /// through its parent chain — a change to any ancestor also counts
    /// as a change to this set.
    pub fn set_chain_eq(&self, other: &PoView, name: &str) -> bool {
        self.sets.contains_key(name)
            && other.sets.contains_key(name)
            && self.chain_content(name) == other.chain_content(name)
    }

    /// The predicates and identifiers of the chain from the root down
    /// to `leaf`, in chain order.
    fn chain_content(&self, leaf: &str) -> (Vec<&PoPredicate>, BTreeMap<&str, &str>) {
        let mut predicates = Vec::new();
        let mut identifiers = BTreeMap::new();
        for set_name in self.chain_root_first(Some(leaf)) {
            if let Some(set) = self.sets.get(set_name) {
                predicates.extend(set.predicates.iter());
                for (name, ty) in &set.identifiers {
                    identifiers.insert(name.as_str(), ty.as_str());
                }
            }
        }
        (predicates, identifiers)
    }

    /// The set names from the root down to `leaf`, inclusive.
    fn chain_root_first<'a>(&'a self, leaf: Option<&'a str>) -> Vec<&'a str> {
        let mut chain = Vec::new();
        let mut current = leaf;
        while let Some(name) = current {
            if chain.contains(&name) {
                break; // defend against cyclic parent links
            }
            chain.push(name);
            current = self.sets.get(name).and_then(|set| set.parent.as_deref());
        }
        chain.reverse();
        chain
    }
}

/// A hint resolved to the content it selects.
#[derive(Debug, PartialEq)]
pub enum ResolvedHint<'a> {
    Interval(Option<Vec<&'a PoPredicate>>),
    Predicate(Option<&'a PoPredicate>),
}

/// The element currently being filled while parsing.
enum Scope {
    None,
    Set(String),
    Sequent(String),
}

/// Dispatch one element into the view. `depth` is the element's own
/// depth: the root is 0, its children 1.
fn handle_element(
    view: &mut PoView,
    scope: &mut Scope,
    depth: usize,
    e: &BytesStart<'_>,
) -> Result<()> {
    match e.name().as_ref() {
        b"org.eventb.core.poFile" if depth == 0 => {
            view.stamp = string_attr(e, b"poStamp")?;
        }
        b"org.eventb.core.poPredicateSet" if depth == 1 => {
            let name = string_attr(e, b"name")?.unwrap_or_default();
            let parent = string_attr(e, b"parentSet")?
                .as_deref()
                .and_then(handle_last_segment);
            view.sets.insert(
                name.clone(),
                PoSet {
                    parent,
                    stamp: string_attr(e, b"poStamp")?,
                    ..PoSet::default()
                },
            );
            *scope = Scope::Set(name);
        }
        b"org.eventb.core.poSequent" if depth == 1 => {
            let name = string_attr(e, b"name")?.unwrap_or_default();
            let sequent = PoSequent {
                description: string_attr(e, b"poDesc")?.unwrap_or_default(),
                accurate: string_attr(e, b"accurate")?.as_deref() == Some("true"),
                stamp: string_attr(e, b"poStamp")?,
                ..PoSequent::default()
            };
            view.sequents.insert(name.clone(), sequent);
            *scope = Scope::Sequent(name);
        }
        b"org.eventb.core.poPredicateSet" if depth == 2 => {
            // A sequent's local hypothesis set.
            if let Scope::Sequent(name) = &*scope {
                let parent = string_attr(e, b"parentSet")?
                    .as_deref()
                    .and_then(handle_last_segment);
                if let Some(sequent) = view.sequents.get_mut(name) {
                    sequent.parent_set = parent;
                }
            }
        }
        b"org.eventb.core.poIdentifier" => {
            if let Scope::Set(name) = &*scope
                && let Some(set) = view.sets.get_mut(name)
            {
                set.identifiers.insert(
                    string_attr(e, b"name")?.unwrap_or_default(),
                    string_attr(e, b"type")?.unwrap_or_default(),
                );
            }
        }
        b"org.eventb.core.poPredicate" => {
            let row = predicate_row(e)?;
            match &*scope {
                Scope::Set(name) => {
                    if let Some(set) = view.sets.get_mut(name) {
                        set.predicate_names
                            .push(string_attr(e, b"name")?.unwrap_or_default());
                        set.predicates.push(row);
                    }
                }
                Scope::Sequent(name) => {
                    if let Some(sequent) = view.sequents.get_mut(name) {
                        // Depth 2 is the goal; deeper rows live inside
                        // the local SEQHYP set.
                        if depth == 2 {
                            sequent.goal = Some(row);
                        } else {
                            sequent.local_hypotheses.push(row);
                        }
                    }
                }
                Scope::None => {}
            }
        }
        b"org.eventb.core.poSource" => {
            if let Scope::Sequent(name) = &*scope
                && let Some(sequent) = view.sequents.get_mut(name)
            {
                sequent.sources.push((
                    string_attr(e, b"poRole")?.unwrap_or_default(),
                    normalize_handle(string_attr(e, b"source")?),
                ));
            }
        }
        b"org.eventb.core.poSelHint" => {
            if let Scope::Sequent(name) = &*scope
                && let Some(sequent) = view.sequents.get_mut(name)
            {
                let start = normalize_handle(string_attr(e, b"poSelHintFst")?).unwrap_or_default();
                let hint = match normalize_handle(string_attr(e, b"poSelHintSnd")?) {
                    Some(end) => PoHint::Interval { start, end },
                    None => PoHint::Predicate(start),
                };
                sequent.hints.push(hint);
            }
        }
        _ => {}
    }
    Ok(())
}

fn predicate_row(e: &BytesStart<'_>) -> Result<PoPredicate> {
    let raw = string_attr(e, b"predicate")?.unwrap_or_default();
    let ast = parse_predicate_str(raw.trim()).map_err(|err| ProjectError::ReparseFormula {
        kind: "predicate",
        input: raw.clone(),
        err,
    })?;
    Ok(PoPredicate {
        predicate: strip_type_ascriptions_pred(ast),
        source: normalize_handle(string_attr(e, b"source")?),
    })
}

// Drop the leading `/PROJECT/` segment of a handle so views from
// differently-named projects compare (same rule as `.bcm` sources).
use crate::sc_view::normalize_source as normalize_handle;

/// The last `#name` segment of a handle, unescaped.
fn handle_last_segment(handle: &str) -> Option<String> {
    handle_segments(handle).pop().map(|(_, name)| name)
}

//! Reading `.bpr` proof files into stored proofs.
//!
//! Only the modern storage layout is supported: reasoners interned as
//! `prReas` children referenced by `prRule` names, predicates and
//! expressions interned as `prPred`/`prExpr` children, and the proof's
//! dependencies stored as attributes of `prProof`. Older layouts (the
//! versioned reasoner id written directly as the `prRule` element
//! name) and proofs carrying an extended mathematical language (a
//! `lang` element with content) classify per proof as
//! [`ProofBody::Unsupported`] rather than failing the file.
//!
//! Proof files reach over a hundred megabytes and their rule trees
//! nest arbitrarily deep, so parsing is one streaming pass driven by
//! an explicit frame stack — no parser recursion — and the caller
//! chooses per proof how much to materialize ([`Keep`]).

use std::collections::{BTreeMap, HashMap, HashSet};
use std::io::BufRead;

use quick_xml::Reader;
use quick_xml::events::{BytesStart, Event};

use rossi::formula::{Predicate, SealedTypeEnvironment, Type, TypeEnvironmentBuilder};
use rossi::{Expression, parse_expression_str, parse_predicate_str};

use crate::confidence::Confidence;
use crate::deps::ProofDependencies;
use crate::hyp_action::HypAction;
use crate::registry::{self, ReasonerDesc};
use crate::rule::{Antecedent, Rule};
use crate::sequent::TypedIdent;
use crate::skeleton::{Skeleton, StoredInput, StoredRule};
use crate::xml::{attr, attrs, get};

/// How much of one proof to materialize.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub enum Keep {
    /// Record only the root attributes (name, confidence, manual).
    #[default]
    Skip,
    /// Additionally resolve the stored dependencies — the status
    /// path. The rule tree is skipped unread, and so is every intern
    /// entry the dependencies do not name: a malformed one fails only
    /// a full read.
    Deps,
    /// Materialize the whole proof, skeleton included.
    Full,
}

/// One `prProof` entry of a `.bpr` file, in document order.
#[derive(Debug)]
pub struct ProofEntry {
    /// The proof obligation's name.
    pub name: String,
    /// The recorded root confidence; `None` when the proof was never
    /// attempted (nothing else is stored then).
    pub confidence: Option<i32>,
    /// Whether the proof is marked as manual.
    pub manual: bool,
    /// The proof's content, per the caller's [`Keep`] choice.
    pub body: ProofBody,
}

/// The materialized content of one proof.
#[derive(Debug)]
pub enum ProofBody {
    /// The caller asked to skip this proof.
    Skipped,
    /// The proof cannot be represented: old-vintage storage, an
    /// extended language, or content rossi cannot parse. The reason
    /// is human-readable.
    Unsupported(String),
    /// The proof loaded.
    Loaded(Box<StoredProof>),
}

/// A loaded proof: its stored dependencies and, in [`Keep::Full`]
/// mode, its skeleton.
#[derive(Debug)]
pub struct StoredProof {
    /// The dependencies as recorded on the proof root — what the
    /// status update consults without touching the rule tree.
    pub deps: ProofDependencies,
    /// The rule tree; `None` in [`Keep::Deps`] mode.
    pub skeleton: Option<Skeleton>,
}

/// A `.bpr`-level failure. Individual proofs degrade to
/// [`ProofBody::Unsupported`]; this error means the file itself is
/// unreadable.
#[derive(Debug, thiserror::Error)]
pub enum BprError {
    /// The XML is malformed.
    #[error("XML error: {0}")]
    Xml(#[from] quick_xml::Error),
    /// Reading or writing the document failed.
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    /// Not a proof file, or an unknown file version.
    #[error("unsupported proof file: {0}")]
    Unsupported(String),
    /// The document ended before the root element was closed.
    #[error("truncated proof file")]
    Truncated,
}

pub(crate) const PR_FILE: &str = "org.eventb.core.prFile";
pub(crate) const PR_PROOF: &str = "org.eventb.core.prProof";
const PR_RULE: &str = "org.eventb.core.prRule";
const PR_ANTE: &str = "org.eventb.core.prAnte";
const PR_HYP_ACTION: &str = "org.eventb.core.prHypAction";
const PR_IDENT: &str = "org.eventb.core.prIdent";
const PR_PRED: &str = "org.eventb.core.prPred";
const PR_EXPR: &str = "org.eventb.core.prExpr";
const PR_REAS: &str = "org.eventb.core.prReas";
const PR_STRING: &str = "org.eventb.core.prString";
const PR_PRED_REF: &str = "org.eventb.core.prPredRef";
const PR_EXPR_REF: &str = "org.eventb.core.prExprRef";
const LANG: &str = "org.eventb.core.lang";

pub(crate) const NAME: &str = "name";
const CONFIDENCE: &str = "org.eventb.core.confidence";
const PR_FRESH: &str = "org.eventb.core.prFresh";
const PR_GOAL: &str = "org.eventb.core.prGoal";
const PR_HYPS: &str = "org.eventb.core.prHyps";
const PR_SETS: &str = "org.eventb.core.prSets";
const PS_MANUAL: &str = "org.eventb.core.psManual";
const PR_DISPLAY: &str = "org.eventb.core.prDisplay";
const PR_UNSEL: &str = "org.eventb.core.prUnsel";
const PR_INF_HYPS: &str = "org.eventb.core.prInfHyps";
const PR_HIDDEN: &str = "org.eventb.core.prHidden";
const PR_RID: &str = "org.eventb.core.prRID";
const PR_SVALUE: &str = "org.eventb.core.prSValue";
const PR_REF: &str = "org.eventb.core.prRef";
const PREDICATE: &str = "org.eventb.core.predicate";
const EXPRESSION: &str = "org.eventb.core.expression";
const TYPE: &str = "org.eventb.core.type";

/// Reads every proof of a `.bpr` document, materializing each per the
/// caller's [`Keep`] choice for its name.
pub fn read_bpr(
    reader: impl BufRead,
    keep: impl FnMut(&str) -> Keep,
) -> Result<Vec<ProofEntry>, BprError> {
    let mut entries = Vec::new();
    visit_bpr(reader, keep, |entry| entries.push(entry))?;
    Ok(entries)
}

/// Reads a `.bpr` document proof by proof, handing each to `sink` as
/// its element closes — a component's proofs never need to be in
/// memory together, though the parses they share are held until the
/// document ends. A read failure still fails the whole document: the
/// proofs already handed out must be discarded.
pub fn visit_bpr(
    reader: impl BufRead,
    mut keep: impl FnMut(&str) -> Keep,
    mut sink: impl FnMut(ProofEntry),
) -> Result<(), BprError> {
    let mut xml = Reader::from_reader(reader);
    let mut buf = Vec::new();
    let mut stack: Vec<Frame> = Vec::new();
    let mut visit = Visit {
        keep: &mut keep,
        sink: &mut sink,
        parses: Parses::default(),
    };
    let mut saw_root = false;
    let mut root_closed = false;

    loop {
        match xml.read_event_into(&mut buf)? {
            Event::Start(e) => {
                open(
                    &e,
                    false,
                    &mut stack,
                    &mut visit,
                    &mut saw_root,
                    &mut root_closed,
                )?;
            }
            Event::Empty(e) => {
                open(
                    &e,
                    true,
                    &mut stack,
                    &mut visit,
                    &mut saw_root,
                    &mut root_closed,
                )?;
            }
            Event::End(_) => match stack.pop() {
                Some(frame) => close(frame, &mut stack, &mut visit),
                // With no frame open this is the file root's end tag:
                // quick-xml has already matched it against its start.
                None => root_closed = true,
            },
            Event::Eof => {
                // quick-xml reports a bare EOF even with elements
                // still open; a truncated file must not read as a
                // complete file with fewer proofs.
                if !(saw_root && root_closed) {
                    return Err(BprError::Truncated);
                }
                break;
            }
            _ => {}
        }
        buf.clear();
    }
    Ok(())
}

/// The attributes of one element, unescaped, in document order.
/// Splits a comma-separated attribute; an empty attribute is empty.
fn csv(s: &str) -> Vec<String> {
    if s.is_empty() {
        Vec::new()
    } else {
        s.split(',').map(str::to_string).collect()
    }
}

/// What one [`visit_bpr`] call carries through the element handlers:
/// the caller's keep policy and sink, and the document's shared parses.
struct Visit<'a> {
    keep: &'a mut dyn FnMut(&str) -> Keep,
    sink: &'a mut dyn FnMut(ProofEntry),
    parses: Parses,
}

/// The parses of one document, shared by all its proofs: a component's
/// proofs restate the same few hundred hypotheses thousands of times
/// over. A failure is remembered too, and reported by every proof
/// meeting the formula, as before.
#[derive(Default)]
struct Parses {
    preds: HashMap<String, Parsed<Predicate>>,
    exprs: HashMap<String, Parsed<Expression>>,
}

/// One formula's parse, and its type-checks by the environment each
/// observed. The checker consults the environment only for the
/// formula's free identifiers (the given sets its type annotations
/// spell are among them), so a check's outcome is a function of their
/// bindings: proofs that agree on those share one formula; two proofs
/// binding a name differently check separately.
struct Parsed<T> {
    parsed: Result<T, String>,
    typed: Vec<Check<T>>,
}

/// The bindings of a formula's free identifiers, in that order, and the
/// check they yielded.
type Check<T> = (Vec<Option<Type>>, Result<T, String>);

/// What the intern tables need of a formula kind.
trait Formula: Clone {
    const KIND: &'static str;
    fn parse(s: &str) -> Result<Self, rossi::ParseError>;
    fn free_identifiers(&self) -> &[String];
    fn type_check(&self, env: &SealedTypeEnvironment) -> Option<Self>;
}

impl Formula for Predicate {
    const KIND: &'static str = "predicate";
    fn parse(s: &str) -> Result<Self, rossi::ParseError> {
        parse_predicate_str(s)
    }
    fn free_identifiers(&self) -> &[String] {
        Predicate::free_identifiers(self)
    }
    fn type_check(&self, env: &SealedTypeEnvironment) -> Option<Self> {
        Predicate::type_check(self, env)
            .typed
            .map(|typed| typed.strip_ascriptions())
    }
}

impl Formula for Expression {
    const KIND: &'static str = "expression";
    fn parse(s: &str) -> Result<Self, rossi::ParseError> {
        parse_expression_str(s)
    }
    fn free_identifiers(&self) -> &[String] {
        Expression::free_identifiers(self)
    }
    fn type_check(&self, env: &SealedTypeEnvironment) -> Option<Self> {
        Expression::type_check(self, env)
            .typed
            .map(|typed| typed.strip_ascriptions())
    }
}

/// The type-checked `formula` under `env`, from the document's shared
/// parses.
fn intern<T: Formula>(
    memo: &mut HashMap<String, Parsed<T>>,
    formula: &str,
    env: &SealedTypeEnvironment,
) -> Result<T, String> {
    let record = match memo.get_mut(formula) {
        Some(record) => record,
        None => memo.entry(formula.to_string()).or_insert_with(|| Parsed {
            parsed: T::parse(formula).map_err(|err| format!("{} `{formula}`: {err}", T::KIND)),
            typed: Vec::new(),
        }),
    };
    let parsed = record.parsed.as_ref().map_err(String::clone)?;
    let names = parsed.free_identifiers();
    let hit = record.typed.iter().find(|(bindings, _)| {
        bindings
            .iter()
            .zip(names)
            .all(|(bound, name)| bound.as_ref() == env.get(name))
    });
    let typed = match hit {
        Some((_, typed)) => typed,
        None => {
            let bindings = names.iter().map(|name| env.get(name).cloned()).collect();
            let typed = parsed
                .type_check(env)
                .ok_or_else(|| format!("{} `{formula}` does not type-check", T::KIND));
            record.typed.push((bindings, typed));
            &record.typed.last().expect("just pushed").1
        }
    };
    typed.clone()
}

#[derive(Debug, Default)]
struct RawProof {
    name: String,
    confidence: Option<i32>,
    manual: bool,
    fresh: String,
    goal: Option<String>,
    hyps: String,
    /// The intern entries the dependencies name: the goal and the
    /// used hypotheses.
    referenced: HashSet<String>,
    sets: String,
    base_idents: Vec<(String, String)>,
    rule: Option<RawRule>,
    preds: Vec<TableEntry>,
    exprs: Vec<TableEntry>,
    reasoners: Vec<(String, String)>,
    /// Names of rule elements harvested while the tree itself is
    /// skipped: interned `prReas` keys in modern storage, reasoner
    /// ids named directly on the rules in the old storage.
    skipped_rule_names: Vec<String>,
    /// First reason this proof cannot be represented, if any.
    poison: Option<String>,
    keep: Keep,
}

impl RawProof {
    /// Whether the child element `name` is swallowed unread. A skipped
    /// proof needs nothing below its root attributes, and without the
    /// rule tree the dependencies consult only the goal and the used
    /// hypotheses among the predicate entries — never an expression.
    fn swallows(&self, name: &[u8], e: &BytesStart<'_>) -> bool {
        match self.keep {
            Keep::Skip => true,
            Keep::Deps => {
                name == PR_EXPR.as_bytes()
                    || (name == PR_PRED.as_bytes()
                        && !attr(e, NAME).is_some_and(|entry| self.referenced.contains(&entry)))
            }
            Keep::Full => false,
        }
    }
}

#[derive(Debug, Default)]
struct TableEntry {
    name: String,
    formula: String,
    idents: Vec<(String, String)>,
}

#[derive(Debug, Default)]
struct RawRule {
    reasoner_ref: String,
    confidence: Option<i32>,
    display: String,
    goal: Option<String>,
    hyps: String,
    antecedents: Vec<RawAnte>,
    strings: Vec<(String, String)>,
    pred_refs: Vec<(String, String)>,
    expr_refs: Vec<(String, String)>,
}

#[derive(Debug, Default)]
struct RawAnte {
    goal: Option<String>,
    hyps: String,
    unsel: String,
    idents: Vec<(String, String)>,
    actions: Vec<RawAction>,
    child: Option<RawRule>,
}

#[derive(Debug, Default)]
struct RawAction {
    kind: String,
    hyps: String,
    inf_hyps: String,
    hidden: String,
    idents: Vec<(String, String)>,
}

#[derive(Debug)]
enum Frame {
    Proof(Box<RawProof>),
    Rule(RawRule),
    Ante(RawAnte),
    Action(RawAction),
    Pred(TableEntry),
    Expr(TableEntry),
    Lang,
    /// An attribute-only element opened with a start tag.
    Leaf,
    /// A subtree being skipped; counts the nesting below its root.
    Skip(u32),
}

/// Marks the enclosing proof unrepresentable, keeping the first reason.
fn poison(stack: &mut [Frame], reason: String) {
    for frame in stack.iter_mut() {
        if let Frame::Proof(proof) = frame {
            proof.poison.get_or_insert(reason);
            return;
        }
    }
}

fn open(
    e: &BytesStart<'_>,
    empty: bool,
    stack: &mut Vec<Frame>,
    visit: &mut Visit<'_>,
    saw_root: &mut bool,
    root_closed: &mut bool,
) -> Result<(), BprError> {
    let name = e.name();
    let name = name.as_ref();

    // Inside a skipped subtree, track depth — but still harvest the
    // rule names: old rule storage spells reasoner ids as rule element
    // names, and a file upgrade derives the proof's
    // used-reasoner set from them, so a dependencies-only read must
    // see them too. Which names are reasoner ids rather than interned
    // `r0`-style keys is decided against the proof's `prReas` table
    // once the proof is complete.
    if let Some(Frame::Skip(depth)) = stack.last_mut() {
        if !empty {
            *depth += 1;
        }
        if name == PR_RULE.as_bytes()
            && let Some(id) = attr(e, NAME)
            && let Some(Frame::Proof(proof)) = stack
                .iter_mut()
                .rev()
                .find(|frame| matches!(frame, Frame::Proof(_)))
        {
            proof.skipped_rule_names.push(id);
        }
        return Ok(());
    }

    if !*saw_root {
        if name != PR_FILE.as_bytes() {
            return Err(BprError::Unsupported(format!(
                "root element {}",
                String::from_utf8_lossy(name)
            )));
        }
        let attrs = attrs(e);
        if get(&attrs, "version") != Some("1") {
            return Err(BprError::Unsupported(format!(
                "file version {:?}",
                get(&attrs, "version")
            )));
        }
        *saw_root = true;
        // A self-closing root is a complete, proof-less file.
        if empty {
            *root_closed = true;
        }
        return Ok(());
    }

    // Swallow the subtrees the keep level never consults without
    // materializing attributes or intern tables (the bulk of a
    // `.bpr`), exactly as if each were a poisoned region:
    // `resolve_proof` maps `Keep::Skip` to `ProofBody::Skipped`
    // unconditionally, and a dependencies-only read resolves nothing
    // through the swallowed entries.
    if let Some(Frame::Proof(proof)) = stack.last()
        && proof.swallows(name, e)
    {
        if !empty {
            stack.push(Frame::Skip(0));
        }
        return Ok(());
    }

    let attrs = attrs(e);
    let unexpected = || {
        Disp::Poison(format!(
            "unexpected element {}",
            String::from_utf8_lossy(name)
        ))
    };
    let disp = match stack.last_mut() {
        None => {
            // Directly under the file root: only proofs.
            if name != PR_PROOF.as_bytes() {
                return Err(BprError::Unsupported(format!(
                    "element {} under the file root",
                    String::from_utf8_lossy(name)
                )));
            }
            let mut proof = RawProof {
                name: get(&attrs, NAME).unwrap_or_default().to_string(),
                manual: get(&attrs, PS_MANUAL) == Some("true"),
                fresh: get(&attrs, PR_FRESH).unwrap_or_default().to_string(),
                goal: get(&attrs, PR_GOAL).map(str::to_string),
                hyps: get(&attrs, PR_HYPS).unwrap_or_default().to_string(),
                sets: get(&attrs, PR_SETS).unwrap_or_default().to_string(),
                ..RawProof::default()
            };
            proof.referenced = csv(&proof.hyps)
                .into_iter()
                .chain(proof.goal.clone())
                .collect();
            match parse_confidence(&attrs) {
                Ok(confidence) => proof.confidence = confidence,
                // A typed attribute read fails on a non-integer
                // value, failing the whole proof load — degrade this
                // proof, never upgrade garbage to a real confidence.
                Err(reason) => proof.poison = Some(reason),
            }
            proof.keep = (visit.keep)(&proof.name);
            Disp::Push(Box::new(Frame::Proof(Box::new(proof))))
        }
        Some(Frame::Proof(proof)) => match name {
            _ if name == PR_IDENT.as_bytes() => {
                record_ident(&attrs, &mut proof.base_idents);
                Disp::Push(Box::new(Frame::Leaf))
            }
            _ if name == PR_RULE.as_bytes() => {
                if proof.keep != Keep::Full {
                    if let Some(id) = get(&attrs, NAME) {
                        proof.skipped_rule_names.push(id.to_string());
                    }
                    Disp::Push(Box::new(Frame::Skip(0)))
                } else if proof.rule.is_some() {
                    Disp::Poison("several root rules".into())
                } else {
                    match raw_rule(&attrs) {
                        Ok(rule) => Disp::Push(Box::new(Frame::Rule(rule))),
                        Err(reason) => Disp::Poison(reason),
                    }
                }
            }
            _ if name == PR_PRED.as_bytes() => {
                Disp::Push(Box::new(Frame::Pred(table_entry(&attrs, PREDICATE))))
            }
            _ if name == PR_EXPR.as_bytes() => {
                Disp::Push(Box::new(Frame::Expr(table_entry(&attrs, EXPRESSION))))
            }
            _ if name == PR_REAS.as_bytes() => {
                proof.reasoners.push((
                    get(&attrs, NAME).unwrap_or_default().to_string(),
                    get(&attrs, PR_RID).unwrap_or_default().to_string(),
                ));
                Disp::Push(Box::new(Frame::Leaf))
            }
            _ if name == LANG.as_bytes() => {
                // Extension providers record an extended language via
                // attributes or children of the `lang` element; a bare
                // element means the default language.
                if attrs.iter().any(|(key, _)| key != NAME) {
                    Disp::Poison("extended mathematical language".into())
                } else {
                    Disp::Push(Box::new(Frame::Lang))
                }
            }
            _ => unexpected(),
        },
        Some(Frame::Rule(rule)) => match name {
            _ if name == PR_ANTE.as_bytes() => Disp::Push(Box::new(Frame::Ante(RawAnte {
                goal: get(&attrs, PR_GOAL).map(str::to_string),
                hyps: get(&attrs, PR_HYPS).unwrap_or_default().to_string(),
                unsel: get(&attrs, PR_UNSEL).unwrap_or_default().to_string(),
                ..RawAnte::default()
            }))),
            _ if name == PR_STRING.as_bytes() => {
                rule.strings.push((
                    input_key(&attrs),
                    get(&attrs, PR_SVALUE).unwrap_or_default().to_string(),
                ));
                Disp::Push(Box::new(Frame::Leaf))
            }
            _ if name == PR_PRED_REF.as_bytes() => {
                rule.pred_refs.push((
                    input_key(&attrs),
                    get(&attrs, PR_REF).unwrap_or_default().to_string(),
                ));
                Disp::Push(Box::new(Frame::Leaf))
            }
            _ if name == PR_EXPR_REF.as_bytes() => {
                rule.expr_refs.push((
                    input_key(&attrs),
                    get(&attrs, PR_REF).unwrap_or_default().to_string(),
                ));
                Disp::Push(Box::new(Frame::Leaf))
            }
            _ => unexpected(),
        },
        Some(Frame::Ante(ante)) => match name {
            _ if name == PR_IDENT.as_bytes() => {
                record_ident(&attrs, &mut ante.idents);
                Disp::Push(Box::new(Frame::Leaf))
            }
            _ if name == PR_HYP_ACTION.as_bytes() => {
                Disp::Push(Box::new(Frame::Action(RawAction {
                    kind: get(&attrs, NAME).unwrap_or_default().to_string(),
                    hyps: get(&attrs, PR_HYPS).unwrap_or_default().to_string(),
                    inf_hyps: get(&attrs, PR_INF_HYPS).unwrap_or_default().to_string(),
                    hidden: get(&attrs, PR_HIDDEN).unwrap_or_default().to_string(),
                    ..RawAction::default()
                })))
            }
            _ if name == PR_RULE.as_bytes() => {
                if ante.child.is_some() {
                    Disp::Poison("several rules under one antecedent".into())
                } else {
                    match raw_rule(&attrs) {
                        Ok(rule) => Disp::Push(Box::new(Frame::Rule(rule))),
                        Err(reason) => Disp::Poison(reason),
                    }
                }
            }
            _ => unexpected(),
        },
        Some(Frame::Action(action)) => {
            if name == PR_IDENT.as_bytes() {
                record_ident(&attrs, &mut action.idents);
                Disp::Push(Box::new(Frame::Leaf))
            } else {
                unexpected()
            }
        }
        Some(Frame::Pred(entry) | Frame::Expr(entry)) => {
            if name == PR_IDENT.as_bytes() {
                record_ident(&attrs, &mut entry.idents);
                Disp::Push(Box::new(Frame::Leaf))
            } else {
                unexpected()
            }
        }
        // Any content under `lang` means an extended language.
        Some(Frame::Lang) => Disp::Poison("extended mathematical language".into()),
        Some(Frame::Leaf) => unexpected(),
        Some(Frame::Skip(_)) => unreachable!("handled above"),
    };

    let frame = match disp {
        Disp::Push(frame) => *frame,
        Disp::Poison(reason) => {
            poison(stack, reason);
            Frame::Skip(0)
        }
    };
    if empty {
        close(frame, stack, visit);
    } else {
        stack.push(frame);
    }
    Ok(())
}

/// What [`open`] decided for one element, applied after the borrow of
/// the enclosing frame ends.
enum Disp {
    Push(Box<Frame>),
    Poison(String),
}

fn raw_rule(attrs: &[(String, String)]) -> Result<RawRule, String> {
    Ok(RawRule {
        reasoner_ref: get(attrs, NAME).unwrap_or_default().to_string(),
        confidence: parse_confidence(attrs)?,
        display: get(attrs, PR_DISPLAY).unwrap_or_default().to_string(),
        goal: get(attrs, PR_GOAL).map(str::to_string),
        hyps: get(attrs, PR_HYPS).unwrap_or_default().to_string(),
        ..RawRule::default()
    })
}

/// The parsed confidence attribute: `Ok(None)` when absent (the
/// storage read then defaults to unattempted), an error when present
/// but not an integer — a typed attribute read fails there.
fn parse_confidence(attrs: &[(String, String)]) -> Result<Option<i32>, String> {
    match get(attrs, CONFIDENCE) {
        None => Ok(None),
        Some(s) => s
            .parse()
            .map(Some)
            .map_err(|_| format!("confidence attribute {s:?}")),
    }
}

fn table_entry(attrs: &[(String, String)], formula_attr: &str) -> TableEntry {
    TableEntry {
        name: get(attrs, NAME).unwrap_or_default().to_string(),
        formula: get(attrs, formula_attr).unwrap_or_default().to_string(),
        idents: Vec::new(),
    }
}

fn record_ident(attrs: &[(String, String)], into: &mut Vec<(String, String)>) {
    into.push((
        get(attrs, NAME).unwrap_or_default().to_string(),
        get(attrs, TYPE).unwrap_or_default().to_string(),
    ));
}

/// The reasoner-input key: the storage prefixes keys with `.`.
fn input_key(attrs: &[(String, String)]) -> String {
    let name = get(attrs, NAME).unwrap_or_default();
    name.strip_prefix('.').unwrap_or(name).to_string()
}

fn close(frame: Frame, stack: &mut Vec<Frame>, visit: &mut Visit<'_>) {
    match (frame, stack.last_mut()) {
        (Frame::Skip(0), _) | (Frame::Leaf, _) | (Frame::Lang, _) => {}
        (Frame::Skip(depth), _) => stack.push(Frame::Skip(depth - 1)),
        (Frame::Proof(proof), _) => (visit.sink)(resolve_proof(*proof, &mut visit.parses)),
        (Frame::Rule(rule), Some(Frame::Proof(proof))) => proof.rule = Some(rule),
        (Frame::Rule(rule), Some(Frame::Ante(ante))) => ante.child = Some(rule),
        (Frame::Ante(ante), Some(Frame::Rule(rule))) => rule.antecedents.push(ante),
        (Frame::Action(action), Some(Frame::Ante(ante))) => ante.actions.push(action),
        (Frame::Pred(entry), Some(Frame::Proof(proof))) => proof.preds.push(entry),
        (Frame::Expr(entry), Some(Frame::Proof(proof))) => proof.exprs.push(entry),
        // Impossible pairings were prevented at open time.
        _ => unreachable!("mismatched proof file frame"),
    }
}

/// Resolves one raw proof into a [`ProofEntry`], degrading to
/// [`ProofBody::Unsupported`] on any representation problem.
fn resolve_proof(raw: RawProof, parses: &mut Parses) -> ProofEntry {
    let name = raw.name.clone();
    let confidence = raw.confidence;
    let manual = raw.manual;
    let body = if raw.keep == Keep::Skip {
        // A poisoned root attribute is visible in every keep mode: the
        // recorded confidence is not trustworthy, and reporting the
        // proof as merely skipped would read as never attempted.
        match raw.poison {
            Some(reason) => ProofBody::Unsupported(reason),
            None => ProofBody::Skipped,
        }
    } else {
        match resolve_body(raw, parses) {
            Ok(proof) => ProofBody::Loaded(Box::new(proof)),
            Err(reason) => ProofBody::Unsupported(reason),
        }
    };
    ProofEntry {
        name,
        confidence,
        manual,
        body,
    }
}

/// The entry's type-check environment: the shared base when it
/// declares no identifiers of its own (an O(1) `Arc` clone), otherwise
/// the base extended with them — built once per distinct identifier
/// list, since the entries of one proof repeat the same few lists.
fn entry_env<'a>(
    base: &SealedTypeEnvironment,
    idents: &'a [(String, String)],
    extended: &mut HashMap<&'a [(String, String)], SealedTypeEnvironment>,
) -> Result<SealedTypeEnvironment, String> {
    if idents.is_empty() {
        return Ok(base.clone());
    }
    if let Some(env) = extended.get(idents) {
        return Ok(env.clone());
    }
    let mut env = base.to_builder();
    for (name, ty) in idents {
        env.insert(
            name,
            Type::parse_rodin(ty).ok_or_else(|| format!("identifier type `{ty}`"))?,
        );
    }
    let env = env.into_snapshot();
    extended.insert(idents, env.clone());
    Ok(env)
}

fn resolve_body(raw: RawProof, parses: &mut Parses) -> Result<StoredProof, String> {
    if let Some(reason) = raw.poison {
        return Err(reason);
    }

    // The base type environment: the proof's used free identifiers.
    let mut builder = TypeEnvironmentBuilder::new();
    let mut used_free_idents = Vec::new();
    for set in csv(&raw.sets) {
        builder.add_given_set(&set);
        used_free_idents.push(TypedIdent::new(set.clone(), Type::carrier_set_type(&set)));
    }
    for (name, ty) in &raw.base_idents {
        let ty = Type::parse_rodin(ty).ok_or_else(|| format!("identifier type `{ty}`"))?;
        builder.insert(name, ty.clone());
        used_free_idents.push(TypedIdent::new(name.clone(), ty));
    }
    let base_env = builder.into_snapshot();
    let mut extended = HashMap::new();

    // The intern tables, type-checked against the base environment
    // extended with each entry's own identifiers.
    let mut preds: BTreeMap<String, Predicate> = BTreeMap::new();
    for entry in &raw.preds {
        let env = entry_env(&base_env, &entry.idents, &mut extended)?;
        preds.insert(
            entry.name.clone(),
            intern(&mut parses.preds, &entry.formula, &env)?,
        );
    }
    let mut exprs = BTreeMap::new();
    for entry in &raw.exprs {
        let env = entry_env(&base_env, &entry.idents, &mut extended)?;
        exprs.insert(
            entry.name.clone(),
            intern(&mut parses.exprs, &entry.formula, &env)?,
        );
    }
    let reasoners: BTreeMap<String, ReasonerDesc> = raw
        .reasoners
        .iter()
        .map(|(name, rid)| (name.clone(), registry::resolve(rid)))
        .collect();

    let pred = |r: &str| {
        preds
            .get(r)
            .cloned()
            .ok_or_else(|| format!("dangling predicate reference `{r}`"))
    };

    // The stored dependencies, straight off the proof root.
    let goal = raw.goal.as_deref().map(pred).transpose()?;
    let used_hypotheses = csv(&raw.hyps)
        .iter()
        .map(|r| pred(r))
        .collect::<Result<Vec<_>, _>>()?;
    let introduced_free_idents: std::collections::BTreeSet<String> =
        csv(&raw.fresh).into_iter().collect();
    let mut used_reasoners: Vec<ReasonerDesc> = raw
        .reasoners
        .iter()
        .map(|(name, _)| reasoners[name].clone())
        .collect();
    // Old rule storage names reasoners on the rules instead of the
    // `prReas` table; without them the version check trusts vacuously
    // where a post-upgrade view distrusts. A skipped rule name is
    // a reasoner id exactly when it is not an interned `prReas` key;
    // descriptor equality is reasoner identity, `(id, version)`.
    for id in &raw.skipped_rule_names {
        if reasoners.contains_key(id) {
            continue;
        }
        let desc = registry::resolve(id);
        if !used_reasoners.contains(&desc) {
            used_reasoners.push(desc);
        }
    }
    let deps = ProofDependencies {
        goal,
        used_hypotheses,
        used_free_idents,
        introduced_free_idents,
        used_reasoners,
    };

    let skeleton = match (raw.keep, raw.rule) {
        (Keep::Full, Some(rule)) => Some(resolve_rule(rule, &preds, &exprs, &reasoners)?),
        (Keep::Full, None) => Some(Skeleton::open()),
        _ => None,
    };

    Ok(StoredProof { deps, skeleton })
}

fn resolve_rule(
    raw: RawRule,
    preds: &BTreeMap<String, Predicate>,
    exprs: &BTreeMap<String, Expression>,
    reasoners: &BTreeMap<String, ReasonerDesc>,
) -> Result<Skeleton, String> {
    // Rule trees nest arbitrarily deep; grow the stack as needed.
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        let pred = |r: &str| {
            preds
                .get(r)
                .cloned()
                .ok_or_else(|| format!("dangling predicate reference `{r}`"))
        };
        let idents = |raw: &[(String, String)]| {
            raw.iter()
                .map(|(name, ty)| {
                    Type::parse_rodin(ty)
                        .map(|ty| TypedIdent::new(name.clone(), ty))
                        .ok_or_else(|| format!("identifier type `{ty}`"))
                })
                .collect::<Result<Vec<_>, _>>()
        };
        let pred_list = |raw: &str| {
            csv(raw)
                .iter()
                .map(|r| pred(r))
                .collect::<Result<Vec<_>, _>>()
        };

        let reasoner = reasoners.get(&raw.reasoner_ref).cloned().ok_or_else(|| {
            format!(
                "unresolved reasoner reference `{}` (old-vintage storage)",
                raw.reasoner_ref
            )
        })?;

        // The recorded confidence caps at uncertain when the
        // reasoner is not trusted (unknown, or a version conflict).
        // An absent attribute reads as unattempted, the storage
        // default — never as
        // discharged, which is only the in-memory default for
        // reasoner-built rules.
        let stored = Confidence(raw.confidence.unwrap_or(Confidence::UNATTEMPTED.0));
        let confidence = if reasoner.is_trusted() {
            stored
        } else {
            Confidence::UNCERTAIN_MAX
        };

        let mut antecedents = Vec::with_capacity(raw.antecedents.len());
        let mut children = Vec::with_capacity(raw.antecedents.len());
        for ante in raw.antecedents {
            let mut hyp_actions = Vec::with_capacity(ante.actions.len());
            for action in &ante.actions {
                hyp_actions.push(resolve_action(action, &pred_list, &idents)?);
            }
            antecedents.push(Antecedent {
                goal: ante.goal.as_deref().map(pred).transpose()?,
                added_hyps: pred_list(&ante.hyps)?,
                unselected_added: pred_list(&ante.unsel)?,
                added_idents: idents(&ante.idents)?,
                hyp_actions,
            });
            children.push(match ante.child {
                Some(child) => resolve_rule(child, preds, exprs, reasoners)?,
                None => Skeleton::open(),
            });
        }

        let mut input = StoredInput::default();
        for (key, value) in raw.strings {
            input.strings.insert(key, value);
        }
        let ref_list = |raw: &str| -> Result<Vec<Option<String>>, String> {
            if raw.is_empty() {
                return Ok(Vec::new());
            }
            Ok(raw
                .split(',')
                .map(|r| (!r.is_empty()).then(|| r.to_string()))
                .collect())
        };
        for (key, refs) in raw.pred_refs {
            let resolved = ref_list(&refs)?
                .into_iter()
                .map(|r| r.as_deref().map(pred).transpose())
                .collect::<Result<Vec<_>, _>>()?;
            input.preds.insert(key, resolved);
        }
        for (key, refs) in raw.expr_refs {
            let resolved = ref_list(&refs)?
                .into_iter()
                .map(|r| {
                    r.map(|r| {
                        exprs
                            .get(&r)
                            .cloned()
                            .ok_or_else(|| format!("dangling expression reference `{r}`"))
                    })
                    .transpose()
                })
                .collect::<Result<Vec<_>, _>>()?;
            input.exprs.insert(key, resolved);
        }

        let rule = Rule {
            reasoner,
            goal: raw.goal.as_deref().map(pred).transpose()?,
            needed_hyps: pred_list(&raw.hyps)?,
            confidence,
            display: raw.display,
            antecedents,
        };
        Ok(Skeleton {
            rule: Some(StoredRule { rule, input }),
            children,
        })
    })
}

fn resolve_action(
    action: &RawAction,
    pred_list: &impl Fn(&str) -> Result<Vec<Predicate>, String>,
    idents: &impl Fn(&[(String, String)]) -> Result<Vec<TypedIdent>, String>,
) -> Result<HypAction, String> {
    let kind = action.kind.as_str();
    if kind.starts_with("SELECT") {
        Ok(HypAction::Select(pred_list(&action.hyps)?))
    } else if kind.starts_with("DESELECT") {
        Ok(HypAction::Deselect(pred_list(&action.hyps)?))
    } else if kind.starts_with("HIDE") {
        Ok(HypAction::Hide(pred_list(&action.hyps)?))
    } else if kind.starts_with("SHOW") {
        Ok(HypAction::Show(pred_list(&action.hyps)?))
    } else if kind.starts_with("FORWARD_INF") {
        Ok(HypAction::ForwardInf {
            hyps: pred_list(&action.hyps)?,
            added_idents: idents(&action.idents)?,
            inferred: pred_list(&action.inf_hyps)?,
        })
    } else if kind.starts_with("REWRITE") {
        // The storage removes the disappearing hypotheses from the
        // action's sources; reading unions them back.
        let disappearing = pred_list(&action.hidden)?;
        let mut hyps = pred_list(&action.hyps)?;
        hyps.extend(disappearing.iter().cloned());
        Ok(HypAction::Rewrite {
            hyps,
            added_idents: idents(&action.idents)?,
            inferred: pred_list(&action.inf_hyps)?,
            disappearing,
        })
    } else {
        Err(format!("unknown hypothesis action `{kind}`"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{env, pred};
    use indoc::{formatdoc, indoc};

    fn file(body: &str) -> String {
        formatdoc!(
            r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
            <org.eventb.core.prFile version="1">
            {body}
            </org.eventb.core.prFile>"#
        )
    }

    fn read(xml: &str, keep: Keep) -> Vec<ProofEntry> {
        read_bpr(xml.as_bytes(), |_| keep).expect("readable file")
    }

    fn loaded(entry: &ProofEntry) -> &StoredProof {
        match &entry.body {
            ProofBody::Loaded(proof) => proof,
            other => panic!("expected a loaded proof, got {other:?}"),
        }
    }

    fn unsupported(entry: &ProofEntry) -> &str {
        match &entry.body {
            ProofBody::Unsupported(reason) => reason,
            other => panic!("expected an unsupported proof, got {other:?}"),
        }
    }

    /// A small but complete modern proof: an auto-rewrite step over a
    /// partition hypothesis, then a goal simplification closed by
    /// ⊤ goal — the shape written today.
    const MODERN: &str = indoc! {r#"
        <org.eventb.core.prProof name="INITIALISATION/inv1/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
        <org.eventb.core.prRule name="r0" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="Partition rewrites" org.eventb.core.prHyps="">
        <org.eventb.core.prAnte name="'">
        <org.eventb.core.prHypAction name="FORWARD_INF0" org.eventb.core.prHyps="p1" org.eventb.core.prInfHyps="p2,p3"/>
        <org.eventb.core.prHypAction name="HIDE1" org.eventb.core.prHyps="p1"/>
        <org.eventb.core.prHypAction name="SELECT2" org.eventb.core.prHyps="p2,p3"/>
        <org.eventb.core.prRule name="r1" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="simplification rewrites" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
        <org.eventb.core.prAnte name="'" org.eventb.core.prGoal="p4">
        <org.eventb.core.prRule name="r2" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="⊤ goal" org.eventb.core.prGoal="p4" org.eventb.core.prHyps=""/>
        </org.eventb.core.prAnte>
        </org.eventb.core.prRule>
        </org.eventb.core.prAnte>
        <org.eventb.core.prString name=".pos" org.eventb.core.prSValue=""/>
        </org.eventb.core.prRule>
        <org.eventb.core.prPred name="p4" org.eventb.core.predicate="⊤"/>
        <org.eventb.core.prPred name="p3" org.eventb.core.predicate="¬ON=OFF">
        <org.eventb.core.prIdent name="OFF" org.eventb.core.type="Status"/>
        <org.eventb.core.prIdent name="ON" org.eventb.core.type="Status"/>
        </org.eventb.core.prPred>
        <org.eventb.core.prPred name="p0" org.eventb.core.predicate="0∈ℕ"/>
        <org.eventb.core.prPred name="p2" org.eventb.core.predicate="Status={ON,OFF}">
        <org.eventb.core.prIdent name="OFF" org.eventb.core.type="Status"/>
        <org.eventb.core.prIdent name="ON" org.eventb.core.type="Status"/>
        <org.eventb.core.prIdent name="Status" org.eventb.core.type="ℙ(Status)"/>
        </org.eventb.core.prPred>
        <org.eventb.core.prPred name="p1" org.eventb.core.predicate="partition(Status,{ON},{OFF})">
        <org.eventb.core.prIdent name="OFF" org.eventb.core.type="Status"/>
        <org.eventb.core.prIdent name="ON" org.eventb.core.type="Status"/>
        <org.eventb.core.prIdent name="Status" org.eventb.core.type="ℙ(Status)"/>
        </org.eventb.core.prPred>
        <org.eventb.core.prReas name="r2" org.eventb.core.prRID="org.eventb.core.seqprover.trueGoal"/>
        <org.eventb.core.prReas name="r0" org.eventb.core.prRID="org.eventb.core.seqprover.partitionRewrites"/>
        <org.eventb.core.prReas name="r1" org.eventb.core.prRID="org.eventb.core.seqprover.autoRewritesL3:0"/>
        </org.eventb.core.prProof>"#};

    /// A present-but-garbage confidence attribute fails the proof
    /// load (a typed attribute read fails), never upgrading
    /// the value to a real confidence — at the proof root and at a
    /// rule alike.
    #[test]
    fn garbage_confidence_degrades_the_proof() {
        for occurrence in [1, 2] {
            let garbage = MODERN.replacen(
                "org.eventb.core.confidence=\"1000\"",
                "org.eventb.core.confidence=\"reviewed\"",
                occurrence,
            );
            let garbage = garbage.replacen(
                "org.eventb.core.confidence=\"reviewed\"",
                "org.eventb.core.confidence=\"1000\"",
                occurrence - 1,
            );
            let entries = read(&file(&garbage), Keep::Full);
            assert!(
                unsupported(&entries[0]).contains("confidence"),
                "occurrence {occurrence}"
            );
        }
    }

    /// A rule without a confidence attribute reads as unattempted —
    /// the storage default — never as discharged.
    #[test]
    fn absent_rule_confidence_reads_as_unattempted() {
        let absent = MODERN.replacen(
            " org.eventb.core.confidence=\"1000\" org.eventb.core.prDisplay=\"Partition rewrites\"",
            " org.eventb.core.prDisplay=\"Partition rewrites\"",
            1,
        );
        let entries = read(&file(&absent), Keep::Full);
        let proof = loaded(&entries[0]);
        let root = proof.skeleton.as_ref().expect("full skeleton");
        let rule = &root.rule.as_ref().expect("root rule").rule;
        assert_eq!(rule.confidence, Confidence::UNATTEMPTED);
    }

    /// Two proofs of one file spelling the same formula over
    /// differently typed identifiers check separately: the shared
    /// parses are keyed by the bindings a check observes.
    #[test]
    fn shared_parses_respect_each_proofs_bindings() {
        let proof = |name: &str, ty: &str| {
            formatdoc!(
                r#"<org.eventb.core.prProof name="{name}" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
                <org.eventb.core.prIdent name="x" org.eventb.core.type="{ty}"/>
                <org.eventb.core.prPred name="p0" org.eventb.core.predicate="x=x"/>
                </org.eventb.core.prProof>"#
            )
        };
        let xml = file(&format!("{}\n{}", proof("a", "ℤ"), proof("b", "BOOL")));
        let entries = read(&xml, Keep::Deps);
        let goal = |i: usize| loaded(&entries[i]).deps.goal.clone().expect("goal");
        assert_eq!(goal(0), pred(&env(&[("x", "ℤ")]), "x=x"));
        assert_eq!(goal(1), pred(&env(&[("x", "BOOL")]), "x=x"));
        assert_ne!(goal(0), goal(1));
    }

    #[test]
    fn modern_sample_loads_fully() {
        let entries = read(&file(MODERN), Keep::Full);
        assert_eq!(entries.len(), 1);
        let entry = &entries[0];
        assert_eq!(entry.name, "INITIALISATION/inv1/INV");
        assert_eq!(entry.confidence, Some(1000));
        assert!(!entry.manual);

        let proof = loaded(entry);
        let empty = env(&[]);
        assert!(proof.deps.has_deps());
        assert_eq!(proof.deps.goal.as_ref(), Some(&pred(&empty, "0∈ℕ")));
        assert!(proof.deps.used_hypotheses.is_empty());
        assert!(proof.deps.used_free_idents.is_empty());
        assert!(proof.deps.introduced_free_idents.is_empty());
        assert_eq!(proof.deps.used_reasoners.len(), 3);

        let root = proof.skeleton.as_ref().expect("full skeleton");
        let rule = &root.rule.as_ref().expect("root rule").rule;
        assert_eq!(
            rule.reasoner.id(),
            "org.eventb.core.seqprover.partitionRewrites"
        );
        assert_eq!(rule.confidence, Confidence::DISCHARGED_MAX);
        assert_eq!(rule.goal, None);
        assert_eq!(rule.antecedents.len(), 1);
        let actions = &rule.antecedents[0].hyp_actions;
        assert_eq!(actions.len(), 3);
        assert!(
            matches!(&actions[0], HypAction::ForwardInf { hyps, inferred, .. }
            if hyps.len() == 1 && inferred.len() == 2)
        );
        assert!(matches!(&actions[1], HypAction::Hide(hyps) if hyps.len() == 1));
        assert!(matches!(&actions[2], HypAction::Select(hyps) if hyps.len() == 2));
        let input = &root.rule.as_ref().unwrap().input;
        assert_eq!(input.strings.get("pos").map(String::as_str), Some(""));

        // The middle rule's reasoner is a stale version (registered 2,
        // stored 0): untrusted, so its confidence caps at uncertain.
        let middle = &root.children[0];
        let middle_rule = &middle.rule.as_ref().expect("middle rule").rule;
        assert_eq!(
            middle_rule.reasoner.id(),
            "org.eventb.core.seqprover.autoRewritesL3"
        );
        assert!(!middle_rule.reasoner.is_trusted());
        assert_eq!(middle_rule.confidence, Confidence::UNCERTAIN_MAX);

        // The ⊤-goal leaf closes the tree.
        let leaf = &middle.children[0];
        let leaf_rule = &leaf.rule.as_ref().expect("leaf rule").rule;
        assert_eq!(leaf_rule.confidence, Confidence::DISCHARGED_MAX);
        assert!(leaf.children.is_empty());
        assert_eq!(leaf_rule.goal.as_ref(), Some(&pred(&empty, "⊤")));
    }

    #[test]
    fn keep_modes_control_materialization() {
        let entries = read(&file(MODERN), Keep::Skip);
        assert!(matches!(entries[0].body, ProofBody::Skipped));
        assert_eq!(entries[0].confidence, Some(1000));

        let entries = read(&file(MODERN), Keep::Deps);
        let proof = loaded(&entries[0]);
        assert!(proof.deps.has_deps());
        assert!(proof.skeleton.is_none());
    }

    #[test]
    fn rewrite_action_unions_hidden_back() {
        let body = indoc! {r#"
            <org.eventb.core.prProof name="evt/inv/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prHyps="">
            <org.eventb.core.prIdent name="x" org.eventb.core.type="ℤ"/>
            <org.eventb.core.prRule name="r0" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="rewrite" org.eventb.core.prHyps="">
            <org.eventb.core.prAnte name="a">
            <org.eventb.core.prHypAction name="REWRITE0" org.eventb.core.prHyps="p0" org.eventb.core.prInfHyps="p2" org.eventb.core.prHidden="p1"/>
            </org.eventb.core.prAnte>
            </org.eventb.core.prRule>
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="x=1"/>
            <org.eventb.core.prPred name="p1" org.eventb.core.predicate="x=2"/>
            <org.eventb.core.prPred name="p2" org.eventb.core.predicate="x=3"/>
            <org.eventb.core.prReas name="r0" org.eventb.core.prRID="org.eventb.core.seqprover.hyp"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Full);
        let proof = loaded(&entries[0]);
        let root = proof.skeleton.as_ref().unwrap();
        let rule = &root.rule.as_ref().unwrap().rule;
        let ints = env(&[("x", "ℤ")]);
        let HypAction::Rewrite {
            hyps, disappearing, ..
        } = &rule.antecedents[0].hyp_actions[0]
        else {
            panic!("expected a rewrite action")
        };
        // The stored sources exclude the hidden hypothesis; reading
        // unions it back.
        assert_eq!(hyps, &[pred(&ints, "x=1"), pred(&ints, "x=2")]);
        assert_eq!(disappearing, &[pred(&ints, "x=2")]);
    }

    #[test]
    fn old_vintage_storage_is_unsupported() {
        let body = indoc! {r#"
            <org.eventb.core.prProof name="evt/inv/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prRule name="org.eventb.core.seqprover.trueGoal" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="⊤ goal" org.eventb.core.prGoal="p0" org.eventb.core.prHyps=""/>
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="⊤"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Full);
        assert!(unsupported(&entries[0]).contains("old-vintage"));
        // The dependency path does not touch the rule tree, so the
        // same proof still loads in Deps mode — with the used
        // reasoners harvested from the rule names, the way a
        // file upgrade derives them.
        let entries = read(&file(body), Keep::Deps);
        let proof = loaded(&entries[0]);
        let ids: Vec<&str> = proof
            .deps
            .used_reasoners
            .iter()
            .map(|desc| desc.id())
            .collect();
        assert_eq!(ids, ["org.eventb.core.seqprover.trueGoal"]);
    }

    #[test]
    fn old_vintage_nested_rules_feed_the_dependency_read() {
        // Nested old-storage rules (a bare id of a now-versioned
        // reasoner, and a dead plugin's) surface in Deps mode, so the
        // reuse check distrusts them exactly like a reference read
        // distrusts the
        // upgraded proof.
        let body = indoc! {r#"
            <org.eventb.core.prProof name="evt/inv/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prRule name="org.eventb.core.seqprover.autoRewrites" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="d" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prAnte name="0" org.eventb.core.prGoal="p0">
            <org.eventb.core.prRule name="com.b4free.rodin.core.externalPP" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="d" org.eventb.core.prGoal="p0" org.eventb.core.prHyps=""/>
            </org.eventb.core.prAnte>
            </org.eventb.core.prRule>
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="⊤"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Deps);
        let proof = loaded(&entries[0]);
        assert!(
            proof
                .deps
                .used_reasoners
                .iter()
                .all(|desc| !desc.is_trusted())
        );
        assert_eq!(proof.deps.used_reasoners.len(), 2);
    }

    /// Old-storage rules repeating the same versioned reasoner id
    /// collapse to one used-reasoner entry: identity is the decoded
    /// `(id, version)` pair, not the raw element name.
    #[test]
    fn repeated_vintage_rule_ids_collapse() {
        let body = indoc! {r#"
            <org.eventb.core.prProof name="evt/inv/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prRule name="org.eventb.core.seqprover.autoRewrites:1" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="d" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prAnte name="0" org.eventb.core.prGoal="p0">
            <org.eventb.core.prRule name="org.eventb.core.seqprover.autoRewrites:1" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="d" org.eventb.core.prGoal="p0" org.eventb.core.prHyps=""/>
            </org.eventb.core.prAnte>
            </org.eventb.core.prRule>
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="⊤"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Deps);
        let proof = loaded(&entries[0]);
        assert_eq!(proof.deps.used_reasoners.len(), 1);
        let desc = &proof.deps.used_reasoners[0];
        assert_eq!(desc.id(), "org.eventb.core.seqprover.autoRewrites");
        assert_eq!(desc.stored_version(), Some(1));
    }

    /// Files predating dotted reasoner ids name rules with a bare id
    /// and carry no `prReas` table; those ids still reach the
    /// dependency read, resolved like any unregistered id to an
    /// untrusted dummy.
    #[test]
    fn bare_vintage_rule_ids_feed_the_dependency_read() {
        let body = indoc! {r#"
            <org.eventb.core.prProof name="evt/inv/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prRule name="autoRewrites" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="d" org.eventb.core.prGoal="p0" org.eventb.core.prHyps=""/>
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="⊤"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Deps);
        let proof = loaded(&entries[0]);
        assert_eq!(proof.deps.used_reasoners.len(), 1);
        let desc = &proof.deps.used_reasoners[0];
        assert_eq!(desc.id(), "autoRewrites");
        assert!(desc.is_dummy());
        assert!(!desc.is_trusted());
    }

    /// Modern rules reference interned `prReas` keys; those keys are
    /// not reasoner ids and add nothing to the used-reasoner set.
    #[test]
    fn interned_rule_keys_are_not_reasoner_ids() {
        let entries = read(&file(MODERN), Keep::Deps);
        let proof = loaded(&entries[0]);
        assert_eq!(proof.deps.used_reasoners.len(), 3);
        assert!(
            proof
                .deps
                .used_reasoners
                .iter()
                .all(|desc| desc.id().contains('.'))
        );
    }

    #[test]
    fn extended_language_is_unsupported() {
        let with_child = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prHyps="">
            <org.eventb.core.lang name="L">
            <org.eventb.core.theoryRef name="T"/>
            </org.eventb.core.lang>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(with_child), Keep::Deps);
        assert!(unsupported(&entries[0]).contains("extended"));

        let with_attr = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prHyps="">
            <org.eventb.core.lang name="L" org.eventb.core.scope="T"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(with_attr), Keep::Deps);
        assert!(unsupported(&entries[0]).contains("extended"));

        let empty_lang = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prHyps="">
            <org.eventb.core.lang name="L"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(empty_lang), Keep::Deps);
        assert!(matches!(entries[0].body, ProofBody::Loaded(_)));
    }

    #[test]
    fn unattempted_proof_has_no_dependencies() {
        let body = r#"<org.eventb.core.prProof name="evt/inv/INV"/>"#;
        let entries = read(&file(body), Keep::Full);
        let entry = &entries[0];
        assert_eq!(entry.confidence, None);
        let proof = loaded(entry);
        assert!(!proof.deps.has_deps());
        assert_eq!(
            proof.skeleton.as_ref().map(|s| s.rule.is_none()),
            Some(true)
        );
    }

    #[test]
    fn pred_ref_holes_stay_none() {
        let body = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prHyps="">
            <org.eventb.core.prRule name="r0" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="d" org.eventb.core.prHyps="">
            <org.eventb.core.prPredRef name=".instantiations" org.eventb.core.prRef="p0,,p0"/>
            <org.eventb.core.prPredRef name=".none" org.eventb.core.prRef=""/>
            </org.eventb.core.prRule>
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="⊤"/>
            <org.eventb.core.prReas name="r0" org.eventb.core.prRID="org.eventb.core.seqprover.hyp"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Full);
        let proof = loaded(&entries[0]);
        let input = &proof
            .skeleton
            .as_ref()
            .unwrap()
            .rule
            .as_ref()
            .unwrap()
            .input;
        let empty = env(&[]);
        assert_eq!(
            input.preds["instantiations"],
            vec![Some(pred(&empty, "⊤")), None, Some(pred(&empty, "⊤"))]
        );
        assert_eq!(input.preds["none"], Vec::new());
    }

    #[test]
    fn ascriptions_are_stripped_after_type_checking() {
        let body = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prIdent name="x" org.eventb.core.type="ℙ(ℤ)"/>
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="x≠(∅ ⦂ ℙ(ℤ))"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Deps);
        let proof = loaded(&entries[0]);
        let sets = env(&[("x", "ℙ(ℤ)")]);
        assert_eq!(proof.deps.goal.as_ref(), Some(&pred(&sets, "x≠∅")));
    }

    #[test]
    fn problems_degrade_to_unsupported() {
        // A predicate that does not parse.
        let bad_pred = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="⊤ ⊤"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(bad_pred), Keep::Deps);
        assert!(unsupported(&entries[0]).contains("predicate"));

        // A dangling reference.
        let dangling = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p9" org.eventb.core.prHyps="">
            </org.eventb.core.prProof>"#};
        let entries = read(&file(dangling), Keep::Deps);
        assert!(unsupported(&entries[0]).contains("dangling"));

        // An unknown element inside the proof.
        let stray = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prHyps="">
            <org.eventb.core.prMystery name="m"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(stray), Keep::Deps);
        assert!(unsupported(&entries[0]).contains("unexpected element"));
    }

    #[test]
    fn unreferenced_entries_only_fail_full_reads() {
        let body = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="⊤"/>
            <org.eventb.core.prPred name="p1" org.eventb.core.predicate="⊤ ⊤"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Deps);
        loaded(&entries[0]);
        let entries = read(&file(body), Keep::Full);
        assert!(unsupported(&entries[0]).contains("predicate"));
    }

    #[test]
    fn unknown_reasoners_load_untrusted() {
        let body = indoc! {r#"
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prHyps="">
            <org.eventb.core.prRule name="r0" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="d" org.eventb.core.prHyps=""/>
            <org.eventb.core.prReas name="r0" org.eventb.core.prRID="org.eventb.theory.rbp.instantiateTheoremReasoner"/>
            </org.eventb.core.prProof>"#};
        let entries = read(&file(body), Keep::Full);
        let proof = loaded(&entries[0]);
        let desc = &proof.deps.used_reasoners[0];
        assert!(desc.is_dummy());
        assert!(!desc.is_trusted());
        let rule = &proof.skeleton.as_ref().unwrap().rule.as_ref().unwrap().rule;
        assert_eq!(rule.confidence, Confidence::UNCERTAIN_MAX);
    }

    /// quick-xml reports a bare EOF when the input ends between
    /// elements; a truncated file must fail rather than read as a
    /// complete file with fewer proofs.
    #[test]
    fn truncated_files_fail_to_read() {
        let complete = file(MODERN);
        assert_eq!(read(&complete, Keep::Skip).len(), 1);
        // A root element with no proofs still reads.
        let empty_root = r#"<org.eventb.core.prFile version="1"/>"#;
        assert!(read_bpr(empty_root.as_bytes(), |_| Keep::Skip).is_ok());

        // Empty input.
        assert!(matches!(
            read_bpr("".as_bytes(), |_| Keep::Skip),
            Err(BprError::Truncated)
        ));
        // Truncated at an element boundary: a complete proof followed
        // by the missing root end tag must not drop later proofs.
        let cut = complete
            .strip_suffix("</org.eventb.core.prFile>")
            .expect("root end tag");
        assert!(matches!(
            read_bpr(cut.as_bytes(), |_| Keep::Skip),
            Err(BprError::Truncated)
        ));
        // Truncated inside an open proof.
        let cut = &complete[..complete.find("<org.eventb.core.prPred").expect("prPred")];
        assert!(matches!(
            read_bpr(cut.as_bytes(), |_| Keep::Skip),
            Err(BprError::Truncated)
        ));
    }

    #[test]
    fn file_level_problems_fail_the_file() {
        assert!(matches!(
            read_bpr("<foo/>".as_bytes(), |_| Keep::Skip),
            Err(BprError::Unsupported(_))
        ));
        assert!(matches!(
            read_bpr(
                r#"<org.eventb.core.prFile version="2"/>"#.as_bytes(),
                |_| Keep::Skip
            ),
            Err(BprError::Unsupported(_))
        ));
        assert!(matches!(
            read_bpr(
                r#"<org.eventb.core.prFile version="1"><org.eventb.core.prProof"#.as_bytes(),
                |_| Keep::Skip
            ),
            Err(BprError::Xml(_))
        ));
    }
}

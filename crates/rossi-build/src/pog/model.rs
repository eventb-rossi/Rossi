//! The proof-obligation file under construction: sequents, predicate
//! sets, and the handles that tie them together.
//!
//! A `.bpo` file is a flat list of predicate sets and sequents. Sets
//! chain through `parentSet` handles into hypothesis stacks; each
//! sequent's local `SEQHYP` set plugs into a chosen stack, carries the
//! sequent-local hypotheses, and is followed by the goal, traceability
//! sources, and prover hints. Elements land in the file in creation
//! order.

use std::rc::Rc;

use rossi::formula::{Predicate, PredicateKind, tag};

use crate::ScFile;
use crate::handles::HandleUri;
use crate::normalize::canonical_typed_predicate;
use crate::xml_out::{Element, RodinNameGenerator, attr, tag as xtag};

use super::natures::Nature;

/// A predicate destined for a `.bpo` file: the typed formula plus the
/// source element it traces back to.
#[derive(Debug, Clone)]
pub struct PogPredicate {
    pub predicate: Predicate,
    pub source: HandleUri,
}

impl PogPredicate {
    pub fn new(predicate: Predicate, source: HandleUri) -> Self {
        PogPredicate { predicate, source }
    }
}

/// The role a source element played in a proof obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    Default,
    Abstract,
    Concrete,
}

impl Role {
    fn as_str(self) -> &'static str {
        match self {
            Role::Default => "DEFAULT",
            Role::Abstract => "ABSTRACT",
            Role::Concrete => "CONCRETE",
        }
    }
}

/// A traceability reference from a sequent to a source element.
#[derive(Debug, Clone)]
pub struct PogSource {
    pub role: Role,
    pub source: HandleUri,
}

impl PogSource {
    pub fn new(role: Role, source: HandleUri) -> Self {
        PogSource { role, source }
    }
}

/// A prover hint attached to a sequent.
#[derive(Debug, Clone)]
pub enum Hint {
    /// Select every predicate set in the chain from `end` (inclusive)
    /// up to `start` (exclusive).
    Interval { start: HandleUri, end: HandleUri },
    /// Select one predicate.
    Predicate(HandleUri),
}

/// One proof obligation, ready to be added to a [`PoFile`].
#[derive(Debug)]
pub struct ProofObligation {
    /// Sequent name, e.g. `evt/inv2/INV`.
    pub name: String,
    pub nature: Nature,
    /// The hypothesis stack the sequent's `SEQHYP` set plugs into.
    pub global_hypotheses: HandleUri,
    /// Sequent-local hypotheses (not shared between sequents).
    pub local_hypotheses: Vec<PogPredicate>,
    pub goal: PogPredicate,
    pub sources: Vec<PogSource>,
    pub hints: Vec<Hint>,
    pub accurate: bool,
}

/// Whether a goal carries no proof value: `⊤`, or a typing predicate
/// `E ∈ T` / `S ⊆ T` whose right-hand side is a type expression.
pub fn is_trivial(goal: &Predicate) -> bool {
    match goal.kind() {
        PredicateKind::Literal(tag::LiteralPredOp::BTrue) => true,
        PredicateKind::Relational {
            op: tag::RelationalOp::In | tag::RelationalOp::SubsetEq,
            right,
            ..
        } => right.is_type_expression(),
        _ => false,
    }
}

/// A `.bpo` file under construction.
#[derive(Debug)]
pub struct PoFile {
    /// The component name; the emitted files are `<component>.bpo`
    /// and `<component>.bps`.
    component: String,
    /// Handle of the file's root element
    /// (`/prj/M.bpo|org.eventb.core.poFile#M`), the base of every
    /// predicate-set and sequent handle.
    root_handle: HandleUri,
    children: Vec<Rc<Element>>,
    /// Names of the sequents created so far, in creation order — the
    /// rows of the status file.
    sequent_names: Vec<String>,
}

impl PoFile {
    /// Start the PO file of component `component` in `project`.
    pub fn new(project: &str, component: &str) -> Self {
        let filename = format!("{component}.bpo");
        let root_handle = HandleUri::root(project, &filename, xtag::PO_FILE, component);
        PoFile {
            component: component.to_string(),
            root_handle,
            children: Vec::new(),
            sequent_names: Vec::new(),
        }
    }

    /// Handle of the top-level predicate set `name`.
    pub fn set_handle(&self, name: &str) -> HandleUri {
        self.root_handle.child(xtag::PO_PREDICATE_SET, name)
    }

    /// Handle of the `SEQHYP` set of sequent `name`.
    pub fn sequent_hypothesis_handle(&self, name: &str) -> HandleUri {
        self.root_handle
            .child(xtag::PO_SEQUENT, name)
            .child(xtag::PO_PREDICATE_SET, SEQ_HYP_NAME)
    }

    /// Handle of predicate `predicate_name` inside top-level set
    /// `set_name` — the target of a predicate selection hint.
    pub fn predicate_handle(&self, set_name: &str, predicate_name: &str) -> HandleUri {
        self.set_handle(set_name)
            .child(xtag::PO_PREDICATE, predicate_name)
    }

    /// Append a top-level element (a predicate set built elsewhere).
    pub fn push(&mut self, element: impl Into<Rc<Element>>) {
        self.children.push(element.into());
    }

    /// Add a proof obligation, unless its goal is trivial.
    pub fn create_po(&mut self, po: ProofObligation) {
        if is_trivial(&po.goal.predicate) {
            return;
        }

        let mut sequent = Element::new(xtag::PO_SEQUENT)
            .attr(attr::NAME, &po.name)
            .attr_bool(attr::ACCURATE, po.accurate)
            .attr(attr::PO_DESC, po.nature.description())
            .attr(attr::PO_STAMP, "0");

        // Children of the sequent take generated names continuing from
        // the explicitly-named SEQHYP set; the local hypotheses inside
        // SEQHYP name from a fresh per-set counter.
        let mut names = RodinNameGenerator::default();
        names.observe(SEQ_HYP_NAME);

        let mut hypothesis = Element::new(xtag::PO_PREDICATE_SET)
            .attr(attr::NAME, SEQ_HYP_NAME)
            .attr(attr::PARENT_SET, po.global_hypotheses.as_str());
        let mut local_names = RodinNameGenerator::default();
        for local in &po.local_hypotheses {
            hypothesis.push(predicate_element(
                local_names.fresh(),
                &local.predicate,
                &local.source,
            ));
        }
        sequent.push(hypothesis);

        sequent.push(predicate_element(
            names.fresh(),
            &po.goal.predicate,
            &po.goal.source,
        ));

        for source in &po.sources {
            sequent.push(
                Element::new(xtag::PO_SOURCE)
                    .attr(attr::NAME, names.fresh())
                    .attr(attr::PO_ROLE, source.role.as_str())
                    .attr(attr::SOURCE, source.source.as_str()),
            );
        }

        for hint in &po.hints {
            let element = Element::new(xtag::PO_SEL_HINT).attr(attr::NAME, names.fresh());
            let element = match hint {
                Hint::Interval { start, end } => element
                    .attr(attr::PO_SEL_HINT_FST, start.as_str())
                    .attr(attr::PO_SEL_HINT_SND, end.as_str()),
                Hint::Predicate(target) => element.attr(attr::PO_SEL_HINT_FST, target.as_str()),
            };
            sequent.push(element);
        }

        self.sequent_names.push(po.name);
        self.children.push(Rc::new(sequent));
    }

    /// Render the finished obligation file and its status sidecar —
    /// one status row per sequent, unattempted (confidence −99, the
    /// prover's below-any-proof marker).
    pub fn into_sc_files(self, accurate: bool) -> (ScFile, ScFile) {
        let mut status_root = Element::new(xtag::PS_FILE);
        for name in &self.sequent_names {
            status_root.push(
                Element::new(xtag::PS_STATUS)
                    .attr(attr::NAME, name)
                    .attr(attr::CONFIDENCE, "-99")
                    .attr(attr::PO_STAMP, "0")
                    .attr(attr::PS_MANUAL, "false"),
            );
        }
        let status = ScFile {
            filename: format!("{}.bps", self.component),
            contents: status_root.to_document(),
            accurate,
        };

        let mut root = Element::new(xtag::PO_FILE).attr(attr::PO_STAMP, "0");
        for child in self.children {
            root.push(child);
        }
        let obligations = ScFile {
            filename: format!("{}.bpo", self.component),
            contents: root.to_document(),
            accurate,
        };
        (obligations, status)
    }
}

/// The fixed name of every sequent's local hypothesis set.
pub const SEQ_HYP_NAME: &str = "SEQHYP";

/// A `poPredicate` row: canonical predicate text plus its source.
pub(super) fn predicate_element(
    name: String,
    predicate: &Predicate,
    source: &HandleUri,
) -> Element {
    Element::new(xtag::PO_PREDICATE)
        .attr(attr::NAME, name)
        .attr(attr::PREDICATE, canonical_typed_predicate(predicate))
        .attr(attr::SOURCE, source.as_str())
}

#[cfg(test)]
mod tests {
    use rossi::formula::{FormulaFactory, Type};

    use super::*;

    fn ff() -> FormulaFactory {
        FormulaFactory::default_factory()
    }

    fn source() -> HandleUri {
        HandleUri::root("prj", "M.bum", "org.eventb.core.machineFile", "M")
            .child("org.eventb.core.invariant", "'")
    }

    fn int_ident(name: &str) -> rossi::formula::Expression {
        ff().free_identifier(name, None, Some(Type::Int))
    }

    fn nontrivial_goal() -> Predicate {
        ff().relational_predicate(
            tag::RelationalOp::Equal,
            int_ident("x"),
            ff().integer_literal(0, None),
            None,
        )
    }

    fn po(file: &PoFile, goal: Predicate, local: Vec<PogPredicate>) -> ProofObligation {
        ProofObligation {
            name: "evt/inv1/INV".to_string(),
            nature: Nature::InvariantPreservation,
            global_hypotheses: file.set_handle("ALLHYP"),
            local_hypotheses: local,
            goal: PogPredicate::new(goal, source()),
            sources: vec![PogSource::new(Role::Default, source())],
            hints: vec![
                Hint::Interval {
                    start: file.set_handle("ALLHYP"),
                    end: file.sequent_hypothesis_handle("evt/inv1/INV"),
                },
                Hint::Predicate(file.predicate_handle("ALLHYP", "PRD0")),
            ],
            accurate: true,
        }
    }

    #[test]
    fn trivial_goals_are_suppressed() {
        let btrue = ff().literal_predicate(tag::LiteralPredOp::BTrue, None);
        assert!(is_trivial(&btrue));

        // x ∈ ℤ is a typing statement.
        let typing = ff().relational_predicate(
            tag::RelationalOp::In,
            int_ident("x"),
            ff().atomic_expression(tag::AtomicOp::Integer, None, None),
            None,
        );
        assert!(is_trivial(&typing));

        // x ∈ ℕ carries proof value.
        let natural = ff().relational_predicate(
            tag::RelationalOp::In,
            int_ident("x"),
            ff().atomic_expression(tag::AtomicOp::Natural, None, None),
            None,
        );
        assert!(!is_trivial(&natural));

        let mut file = PoFile::new("prj", "M");
        let obligation = po(&file, btrue, Vec::new());
        file.create_po(obligation);
        let rendered = file.into_sc_files(true).0;
        assert!(!rendered.contents.contains("poSequent"));
    }

    #[test]
    fn sequent_children_take_consecutive_generated_names() {
        let mut file = PoFile::new("prj", "M");
        let hyp = PogPredicate::new(nontrivial_goal(), source());
        let obligation = po(&file, nontrivial_goal(), vec![hyp.clone(), hyp]);
        file.create_po(obligation);
        let contents = file.into_sc_files(true).0.contents;

        // SEQHYP, then goal SEQHYQ, source SEQHYR, hints SEQHYS/SEQHYT.
        for needle in [
            r#"<org.eventb.core.poSequent name="evt/inv1/INV" org.eventb.core.accurate="true" org.eventb.core.poDesc="Invariant  preservation" org.eventb.core.poStamp="0">"#,
            r#"<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="/prj/M.bpo|org.eventb.core.poFile#M|org.eventb.core.poPredicateSet#ALLHYP">"#,
            r#"<org.eventb.core.poPredicate name="SEQHYQ" org.eventb.core.predicate="x=0""#,
            r#"<org.eventb.core.poSource name="SEQHYR" org.eventb.core.poRole="DEFAULT""#,
            r#"<org.eventb.core.poSelHint name="SEQHYS" org.eventb.core.poSelHintFst="/prj/M.bpo|org.eventb.core.poFile#M|org.eventb.core.poPredicateSet#ALLHYP" org.eventb.core.poSelHintSnd="/prj/M.bpo|org.eventb.core.poFile#M|org.eventb.core.poSequent#evt\/inv1\/INV|org.eventb.core.poPredicateSet#SEQHYP"/>"#,
            r#"<org.eventb.core.poSelHint name="SEQHYT" org.eventb.core.poSelHintFst="/prj/M.bpo|org.eventb.core.poFile#M|org.eventb.core.poPredicateSet#ALLHYP|org.eventb.core.poPredicate#PRD0"/>"#,
            // Local hypotheses name from a fresh per-set counter.
            r#"<org.eventb.core.poPredicate name="'" org.eventb.core.predicate="x=0""#,
            r#"<org.eventb.core.poPredicate name="(" org.eventb.core.predicate="x=0""#,
        ] {
            assert!(
                contents.contains(needle),
                "missing {needle} in:\n{contents}"
            );
        }
    }
}

//! Incremental hypothesis sets shared between proof obligations.
//!
//! A component's global hypotheses (a context's axioms, a machine's
//! invariants, an event's guards) form an ordered table. A proof
//! obligation about element *n* may hypothesize exactly the elements
//! before it, so each requested prefix becomes a cut point in a chain
//! of predicate sets: the root set, an optional identifier set, one
//! delta set per requested cut, and a final set holding the tail.
//! Sets are materialized lazily — only prefixes some obligation asked
//! for produce a set of their own; everything else lands in the final
//! set. Predicate rows are named `PRD<k>` by their table index, so a
//! predicate's identity is independent of which set it lands in.

use rossi::formula::{Predicate, Type};

use crate::handles::HandleUri;
use crate::normalize::canonical_typed_predicate;
use crate::xml_out::{Element, attr, tag as xtag};

use super::model::PoFile;

/// One row of the hypothesis table.
#[derive(Debug, Clone)]
pub struct HypothesisRow {
    /// The element's Rodin-internal name — cut points requested after
    /// this row name themselves `<prefix><internal_name>`.
    pub internal_name: String,
    pub predicate: Predicate,
    pub source: HandleUri,
}

/// Builder of one hypothesis chain (context, machine, or event scoped).
#[derive(Debug)]
pub struct HypothesisManager {
    /// The chain's root set — created by the caller, not the manager.
    root_name: String,
    /// Name of the identifier set, created between the root and the
    /// first delta when identifiers were registered.
    ident_name: String,
    /// Prefix of cut-point set names.
    hyp_prefix: String,
    /// Name of the final set holding the whole table.
    all_name: String,
    rows: Vec<HypothesisRow>,
    /// Memoized set name per requested prefix; index 0 is the chain
    /// head (identifier set or root), index i > 0 cuts before row i.
    requested: Vec<Option<String>>,
    /// Typed identifiers of the chain head, in insertion order.
    identifiers: Vec<(String, Type)>,
}

/// The predicate-row prefix inside delta sets.
pub const PRD_NAME_PREFIX: &str = "PRD";

/// The root set of a context's chain, and the second set of a
/// machine's (variables and inherited invariants).
pub const ABS_HYP_NAME: &str = "ABSHYP";
/// The root set of a machine's chain (seen contexts' identifiers and
/// axioms).
pub const CTX_HYP_NAME: &str = "CTXHYP";
/// The final set of a component-level chain.
pub const ALL_HYP_NAME: &str = "ALLHYP";
/// The identifier set of a component-level chain.
pub const IDENT_HYP_NAME: &str = "IDENT";
/// The cut-point prefix of a component-level chain.
pub const HYP_PREFIX: &str = "HYP";

impl HypothesisManager {
    pub fn new(
        root_name: impl Into<String>,
        ident_name: impl Into<String>,
        hyp_prefix: impl Into<String>,
        all_name: impl Into<String>,
        rows: Vec<HypothesisRow>,
    ) -> Self {
        let requested = vec![None; rows.len().max(1)];
        HypothesisManager {
            root_name: root_name.into(),
            ident_name: ident_name.into(),
            hyp_prefix: hyp_prefix.into(),
            all_name: all_name.into(),
            rows,
            requested,
            identifiers: Vec::new(),
        }
    }

    /// Register a typed identifier on the chain head. Identifiers must
    /// all be registered before the first hypothesis request — the
    /// head's name is fixed the first time it is asked for.
    pub fn add_identifier(&mut self, name: impl Into<String>, ty: Type) {
        assert!(
            self.requested[0].is_none(),
            "identifiers must be registered before hypotheses are requested"
        );
        let name = name.into();
        if !self.identifiers.iter().any(|(n, _)| *n == name) {
            self.identifiers.push((name, ty));
        }
    }

    fn first_name(&self) -> &str {
        if self.identifiers.is_empty() {
            &self.root_name
        } else {
            &self.ident_name
        }
    }

    /// The set holding exactly the rows before `index`, requesting its
    /// materialization. Returns the set's name.
    pub fn make_hypothesis(&mut self, index: usize) -> String {
        if self.requested[index].is_none() {
            self.requested[index] = Some(if index == 0 {
                self.first_name().to_string()
            } else {
                format!("{}{}", self.hyp_prefix, self.rows[index - 1].internal_name)
            });
        }
        self.requested[index].clone().expect("just set")
    }

    /// The full hypothesis — the final set holding the whole table.
    pub fn full_hypothesis(&self) -> &str {
        &self.all_name
    }

    /// The chain's root set.
    pub fn root_hypothesis(&self) -> &str {
        &self.root_name
    }

    /// Where row `index`'s predicate will land: the first materialized
    /// cut after it, else the final set. Returns `(set_name,
    /// predicate_name)` — the target of a predicate selection hint.
    /// Meaningful once every hypothesis request has been made.
    pub fn predicate_location(&self, index: usize) -> (String, String) {
        let predicate_name = format!("{PRD_NAME_PREFIX}{index}");
        for i in index + 1..self.rows.len() {
            if let Some(name) = &self.requested[i] {
                return (name.clone(), predicate_name);
            }
        }
        (self.all_name.clone(), predicate_name)
    }

    /// Materialize the chain into `po`: the identifier set when
    /// identifiers were registered, each requested cut with its delta
    /// of predicate rows, and the final set with the tail. The final
    /// set always exists, even empty.
    pub fn create_hypotheses(&self, po: &mut PoFile) {
        if !self.identifiers.is_empty() {
            let mut set = predicate_set(&self.ident_name, &po.set_handle(&self.root_name));
            for (name, ty) in &self.identifiers {
                set.push(
                    Element::new(xtag::PO_IDENTIFIER)
                        .attr(attr::NAME, name)
                        .attr(attr::TYPE, ty.to_rodin_canonical()),
                );
            }
            po.push(set);
        }

        let mut previous = 0usize;
        let mut previous_name = self.first_name().to_string();
        for i in 1..self.rows.len() {
            if let Some(name) = self.requested[i].clone() {
                self.emit_delta(po, &name, previous, i, &previous_name);
                previous = i;
                previous_name = name;
            }
        }
        self.emit_delta(
            po,
            &self.all_name,
            previous,
            self.rows.len(),
            &previous_name,
        );
    }

    /// One delta set holding rows `previous..current`.
    fn emit_delta(
        &self,
        po: &mut PoFile,
        name: &str,
        previous: usize,
        current: usize,
        previous_name: &str,
    ) {
        let mut set = predicate_set(name, &po.set_handle(previous_name));
        for (k, row) in self.rows[previous..current].iter().enumerate() {
            set.push(
                Element::new(xtag::PO_PREDICATE)
                    .attr(attr::NAME, format!("{PRD_NAME_PREFIX}{}", previous + k))
                    .attr(attr::PREDICATE, canonical_typed_predicate(&row.predicate))
                    .attr(attr::SOURCE, row.source.as_str()),
            );
        }
        po.push(set);
    }
}

/// A chained top-level predicate set (name, parent, fresh stamp).
fn predicate_set(name: &str, parent: &HandleUri) -> Element {
    Element::new(xtag::PO_PREDICATE_SET)
        .attr(attr::NAME, name)
        .attr(attr::PARENT_SET, parent.as_str())
        .attr(attr::PO_STAMP, "0")
}

#[cfg(test)]
mod tests {
    use rossi::formula::{FormulaFactory, tag};

    use super::*;

    fn row(internal_name: &str, value: i64) -> HypothesisRow {
        let ff = FormulaFactory::default_factory();
        let predicate = ff.relational_predicate(
            tag::RelationalOp::Equal,
            ff.free_identifier("x", None, Some(Type::Int)),
            ff.integer_literal(value, None),
            None,
        );
        HypothesisRow {
            internal_name: internal_name.to_string(),
            predicate,
            source: HandleUri::root("prj", "C.buc", "org.eventb.core.contextFile", "C")
                .child("org.eventb.core.axiom", internal_name),
        }
    }

    fn manager(rows: Vec<HypothesisRow>) -> HypothesisManager {
        HypothesisManager::new("ABSHYP", "IDENT", "HYP", "ALLHYP", rows)
    }

    fn render(manager: &HypothesisManager) -> String {
        let mut po = PoFile::new("prj", "C");
        manager.create_hypotheses(&mut po);
        po.into_sc_file(true).contents
    }

    #[test]
    fn only_requested_cut_points_materialize() {
        let mut m = manager(vec![row("a", 0), row("b", 1), row("c", 2)]);
        assert_eq!(m.make_hypothesis(0), "ABSHYP");
        assert_eq!(m.make_hypothesis(2), "HYPb");
        let contents = render(&m);

        // The chain: HYPb (rows 0..2, parent ABSHYP), ALLHYP (row 2).
        assert!(contents.contains(
            r#"<org.eventb.core.poPredicateSet name="HYPb" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#ABSHYP" org.eventb.core.poStamp="0">"#
        ));
        assert!(contents.contains(
            r#"<org.eventb.core.poPredicateSet name="ALLHYP" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#HYPb" org.eventb.core.poStamp="0">"#
        ));
        // No cut before row 1: no HYPa set.
        assert!(!contents.contains("HYPa"));
        // Global PRD numbering across the deltas.
        assert!(contents.contains(r#"name="PRD0" org.eventb.core.predicate="x=0""#));
        assert!(contents.contains(r#"name="PRD1" org.eventb.core.predicate="x=1""#));
        assert!(contents.contains(r#"name="PRD2" org.eventb.core.predicate="x=2""#));
    }

    #[test]
    fn empty_table_still_gets_the_final_set() {
        let m = manager(Vec::new());
        let contents = render(&m);
        assert!(contents.contains(
            r#"<org.eventb.core.poPredicateSet name="ALLHYP" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#ABSHYP" org.eventb.core.poStamp="0"/>"#
        ));
    }

    #[test]
    fn identifiers_insert_a_set_at_the_chain_head() {
        let mut m = manager(vec![row("a", 0)]);
        m.add_identifier("x", Type::Int);
        m.add_identifier("x", Type::Int); // duplicates collapse
        m.add_identifier("y", Type::Bool);
        assert_eq!(m.make_hypothesis(0), "IDENT");
        let contents = render(&m);

        assert!(contents.contains(
            r#"<org.eventb.core.poPredicateSet name="IDENT" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#ABSHYP" org.eventb.core.poStamp="0">"#
        ));
        assert!(
            contents
                .contains(r#"<org.eventb.core.poIdentifier name="x" org.eventb.core.type="ℤ"/>"#)
        );
        assert!(
            contents.contains(
                r#"<org.eventb.core.poIdentifier name="y" org.eventb.core.type="BOOL"/>"#
            )
        );
        assert_eq!(contents.matches("poIdentifier").count(), 2);
        // ALLHYP chains through the identifier set.
        assert!(contents.contains(
            r#"<org.eventb.core.poPredicateSet name="ALLHYP" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#IDENT" org.eventb.core.poStamp="0">"#
        ));
    }

    #[test]
    fn predicate_location_anticipates_the_holding_set() {
        let mut m = manager(vec![row("a", 0), row("b", 1), row("c", 2)]);
        m.make_hypothesis(2);
        // Row 0 lands in the HYPb delta; rows 2 in ALLHYP.
        assert_eq!(
            m.predicate_location(0),
            ("HYPb".to_string(), "PRD0".to_string())
        );
        assert_eq!(
            m.predicate_location(2),
            ("ALLHYP".to_string(), "PRD2".to_string())
        );
    }
}

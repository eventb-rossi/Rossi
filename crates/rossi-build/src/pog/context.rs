//! Proof obligations of a context: well-definedness of every axiom,
//! and the provability of every theorem.
//!
//! The hypothesis stack starts at `ABSHYP`, which holds everything the
//! context inherits through EXTENDS — the abstract contexts' carrier
//! sets and constants as typed identifiers and their axioms as plain
//! hypotheses — plus the context's own identifiers. The context's own
//! axioms form the incremental table: axiom *n*'s obligations
//! hypothesize exactly the axioms before it.

use std::collections::HashMap;

use crate::ScFile;
use crate::project::Project;
use crate::sc::{CheckedContext, ScModel, context_record::ContextRecord};
use crate::xml_out::{Element, RodinNameGenerator, attr, tag as xtag};

use super::hyp::{ABS_HYP_NAME, ALL_HYP_NAME, HYP_PREFIX, HypothesisManager, HypothesisRow};
use super::model::{Hint, PoFile, PogPredicate, PogSource, ProofObligation, Role, is_trivial};
use super::natures::Nature;

/// Generate `C.bpo` and `C.bps` for a checked context.
pub(super) fn generate(
    project: &Project,
    model: &ScModel,
    context: &CheckedContext,
) -> (ScFile, ScFile) {
    let mut po = PoFile::new(&project.name, context.name());

    // ABSHYP: for each abstract context, its identifiers then its
    // axioms; finally this context's own identifiers. Predicate rows
    // take generated names continuing from the identifiers seen so far.
    let mut abs_hyp = Element::new(xtag::PO_PREDICATE_SET)
        .attr(attr::NAME, ABS_HYP_NAME)
        .attr(attr::PO_STAMP, "0");
    let mut names = RodinNameGenerator::default();
    for abstract_context in model.abstract_contexts(context) {
        push_context_hypotheses(&mut abs_hyp, &mut names, &abstract_context.record);
    }
    push_identifiers(&mut abs_hyp, &mut names, &context.record);
    po.push(abs_hyp);

    let internal_names = axiom_internal_names(context);
    let rows: Vec<HypothesisRow> = context
        .record
        .axioms
        .iter()
        .map(|axiom| HypothesisRow {
            internal_name: internal_names
                .get(axiom.label.as_str())
                .unwrap_or(&axiom.label.as_str())
                .to_string(),
            predicate: axiom.typed.clone(),
            source: axiom.source.clone(),
        })
        .collect();
    let mut manager = HypothesisManager::new(
        ABS_HYP_NAME,
        super::hyp::IDENT_HYP_NAME,
        HYP_PREFIX,
        ALL_HYP_NAME,
        rows,
    );

    for (index, axiom) in context.record.axioms.iter().enumerate() {
        let wd_nature = if axiom.is_theorem {
            Nature::TheoremWellDefinedness
        } else {
            Nature::AxiomWellDefinedness
        };
        let wd = axiom.typed.wd_lemma();
        if !is_trivial(&wd) {
            let hypothesis = manager.make_hypothesis(index);
            po.create_po(ProofObligation {
                name: format!("{}/WD", axiom.label),
                nature: wd_nature,
                global_hypotheses: po.set_handle(&hypothesis),
                local_hypotheses: Vec::new(),
                goal: PogPredicate::new(wd, axiom.source.clone()),
                sources: vec![PogSource::new(Role::Default, axiom.source.clone())],
                hints: vec![Hint::Interval {
                    start: po.set_handle(manager.root_hypothesis()),
                    end: po.set_handle(&hypothesis),
                }],
                accurate: context.accurate,
            });
        }

        if axiom.is_theorem && !is_trivial(&axiom.typed) {
            let hypothesis = manager.make_hypothesis(index);
            po.create_po(ProofObligation {
                name: format!("{}/THM", axiom.label),
                nature: Nature::Theorem,
                global_hypotheses: po.set_handle(&hypothesis),
                local_hypotheses: Vec::new(),
                goal: PogPredicate::new(axiom.typed.clone(), axiom.source.clone()),
                sources: vec![PogSource::new(Role::Default, axiom.source.clone())],
                hints: vec![Hint::Interval {
                    start: po.set_handle(manager.root_hypothesis()),
                    end: po.set_handle(&hypothesis),
                }],
                accurate: context.accurate,
            });
        }
    }

    manager.create_hypotheses(&mut po);
    po.into_sc_files(context.accurate)
}

/// A context's whole contribution to a hypothesis root set: its
/// identifiers, then its axioms as predicate rows with generated names.
pub(super) fn push_context_hypotheses(
    set: &mut Element,
    names: &mut RodinNameGenerator,
    record: &ContextRecord,
) {
    push_identifiers(set, names, record);
    for axiom in &record.axioms {
        set.push(super::model::predicate_element(
            names.fresh(),
            &axiom.typed,
            &axiom.source,
        ));
    }
}

/// A context's carrier sets and constants as `poIdentifier` rows,
/// observed by the set's name counter.
fn push_identifiers(set: &mut Element, names: &mut RodinNameGenerator, record: &ContextRecord) {
    for carrier_set in &record.carrier_sets {
        names.observe(&carrier_set.name);
        set.push(
            Element::new(xtag::PO_IDENTIFIER)
                .attr(attr::NAME, &carrier_set.name)
                .attr(attr::TYPE, carrier_set.ty.to_rodin_canonical()),
        );
    }
    for constant in &record.constants {
        names.observe(&constant.name);
        set.push(
            Element::new(xtag::PO_IDENTIFIER)
                .attr(attr::NAME, &constant.name)
                .attr(attr::TYPE, constant.ty.to_rodin_canonical()),
        );
    }
}

/// The checked-file internal name of each own axiom, by label — the
/// identity cut-point names are built from.
fn axiom_internal_names(context: &CheckedContext) -> HashMap<&str, &str> {
    context
        .body
        .iter()
        .filter(|element| element.tag == xtag::SC_AXIOM)
        .filter_map(|element| {
            Some((
                element.attr_value(attr::LABEL)?,
                element.attr_value(attr::NAME)?,
            ))
        })
        .collect()
}

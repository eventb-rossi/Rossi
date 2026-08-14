//! Proof obligations of a machine: well-definedness and provability of
//! its own invariants, and the well-definedness and finiteness of its
//! variant.
//!
//! The hypothesis stack starts at `CTXHYP` — the seen contexts'
//! identifiers and axioms — followed by `ABSHYP` with every machine
//! variable as a typed identifier and the refinement ancestors'
//! invariants as plain hypotheses (they were proved in the
//! abstraction). The machine's own invariants form the incremental
//! table: invariant *n*'s obligations hypothesize exactly the
//! invariants declared before it.

use rossi::formula::Type;

use crate::ScFile;
use crate::project::{Project, ProjectComponent};
use crate::sc::{CheckedMachine, ScModel};
use crate::xml_out::{Element, RodinNameGenerator, attr, tag as xtag};

use super::context::push_context_hypotheses;
use super::hyp::{
    ABS_HYP_NAME, ALL_HYP_NAME, CTX_HYP_NAME, HYP_PREFIX, HypothesisManager, HypothesisRow,
};
use super::model::{Hint, PoFile, PogPredicate, PogSource, ProofObligation, Role, is_trivial};
use super::natures::Nature;

/// Generate `M.bpo` for a checked machine.
pub(super) fn generate(
    project: &Project,
    pc: &ProjectComponent,
    model: &ScModel,
    machine: &CheckedMachine,
) -> ScFile {
    let mut po = PoFile::new(&project.name, machine.name());

    // CTXHYP: the seen contexts' identifiers and axioms, in hoist order.
    let mut ctx_hyp = Element::new(xtag::PO_PREDICATE_SET)
        .attr(attr::NAME, CTX_HYP_NAME)
        .attr(attr::PO_STAMP, "0");
    let mut ctx_names = RodinNameGenerator::default();
    for context in model.seen_contexts(machine) {
        push_context_hypotheses(&mut ctx_hyp, &mut ctx_names, &context.record);
    }
    po.push(ctx_hyp);

    // ABSHYP: every machine variable as a typed identifier, then the
    // refinement ancestors' invariants as plain hypotheses.
    let mut abs_hyp = Element::new(xtag::PO_PREDICATE_SET)
        .attr(attr::NAME, ABS_HYP_NAME)
        .attr(attr::PARENT_SET, po.set_handle(CTX_HYP_NAME).as_str())
        .attr(attr::PO_STAMP, "0");
    let mut abs_names = RodinNameGenerator::default();
    for variable in &machine.record.variables {
        abs_names.observe(&variable.name);
        abs_hyp.push(
            Element::new(xtag::PO_IDENTIFIER)
                .attr(attr::NAME, &variable.name)
                .attr(attr::TYPE, variable.ty.to_rodin_canonical()),
        );
    }
    for (_, invariant) in model.inherited_invariants(machine) {
        abs_hyp.push(
            Element::new(xtag::PO_PREDICATE)
                .attr(attr::NAME, abs_names.fresh())
                .attr(
                    attr::PREDICATE,
                    crate::normalize::canonical_typed_predicate(&invariant.typed),
                )
                .attr(attr::SOURCE, invariant.source.as_str()),
        );
    }
    po.push(abs_hyp);

    // The machine's own invariants form the incremental table.
    let internal_names = own_invariant_internal_names(machine);
    let rows: Vec<HypothesisRow> = machine
        .record
        .invariants
        .iter()
        .zip(&internal_names)
        .map(|(invariant, internal_name)| HypothesisRow {
            internal_name: internal_name.clone(),
            predicate: invariant.typed.clone(),
            source: invariant.source.clone(),
        })
        .collect();
    let mut manager = HypothesisManager::new(
        ABS_HYP_NAME,
        super::hyp::IDENT_HYP_NAME,
        HYP_PREFIX,
        ALL_HYP_NAME,
        rows,
    );

    for (index, invariant) in machine.record.invariants.iter().enumerate() {
        let wd_nature = if invariant.is_theorem {
            Nature::TheoremWellDefinedness
        } else {
            Nature::InvariantWellDefinedness
        };
        let wd = invariant.typed.wd_lemma();
        if !is_trivial(&wd) {
            let hypothesis = manager.make_hypothesis(index);
            po.create_po(ProofObligation {
                name: format!("{}/WD", invariant.label),
                nature: wd_nature,
                global_hypotheses: po.set_handle(&hypothesis),
                local_hypotheses: Vec::new(),
                goal: PogPredicate::new(wd, invariant.source.clone()),
                sources: vec![PogSource::new(Role::Default, invariant.source.clone())],
                hints: vec![Hint::Interval {
                    start: po.set_handle(manager.root_hypothesis()),
                    end: po.set_handle(&hypothesis),
                }],
                accurate: machine.accurate,
            });
        }

        if invariant.is_theorem && !is_trivial(&invariant.typed) {
            let hypothesis = manager.make_hypothesis(index);
            po.create_po(ProofObligation {
                name: format!("{}/THM", invariant.label),
                nature: Nature::Theorem,
                global_hypotheses: po.set_handle(&hypothesis),
                local_hypotheses: Vec::new(),
                goal: PogPredicate::new(invariant.typed.clone(), invariant.source.clone()),
                sources: vec![PogSource::new(Role::Default, invariant.source.clone())],
                hints: vec![Hint::Interval {
                    start: po.set_handle(manager.root_hypothesis()),
                    end: po.set_handle(&hypothesis),
                }],
                accurate: machine.accurate,
            });
        }
    }

    generate_variant_pos(pc, machine, &mut po);

    let ff = machine_factory(machine);
    let variables = super::tables::MachineVariables::new(&machine.record);
    let variant_label = machine
        .record
        .variant
        .as_ref()
        .map(|variant| pc.rodin_ids.last_variant_label().unwrap_or(variant.label));
    let variant = machine.record.variant.as_ref().zip(variant_label);
    for event in &machine.record.events {
        let mut scope = super::event::EventScope::new(model, machine, &variables, event, &ff);
        super::event::generate_event(
            &mut po,
            &mut scope,
            &manager,
            &machine.record.invariants,
            variant,
        );
    }

    manager.create_hypotheses(&mut po);
    po.into_sc_file(machine.accurate)
}

/// The formula factory the machine's typed formulas were built with —
/// every formula of one project shares it. Falls back to the core
/// factory for a machine with no formulas at all.
fn machine_factory(machine: &CheckedMachine) -> rossi::formula::FormulaFactory {
    machine
        .record
        .invariants
        .first()
        .map(|invariant| invariant.typed.factory().clone())
        .or_else(|| {
            machine.record.events.iter().find_map(|event| {
                event
                    .guards
                    .first()
                    .map(|guard| guard.typed.factory().clone())
                    .or_else(|| {
                        event
                            .actions
                            .iter()
                            .find_map(|action| action.typed.as_ref())
                            .map(|assignment| assignment.factory().clone())
                    })
            })
        })
        .unwrap_or_else(rossi::formula::FormulaFactory::default_factory)
}

/// `VWD` (well-definedness) and `FIN` (finiteness) of the variant.
fn generate_variant_pos(pc: &ProjectComponent, machine: &CheckedMachine, po: &mut PoFile) {
    let Some(variant) = &machine.record.variant else {
        return;
    };
    let Some(typed) = &variant.typed else {
        return;
    };
    let label = pc
        .rodin_ids
        .last_variant_label()
        .unwrap_or(variant.label)
        .to_string();
    let sources = vec![PogSource::new(Role::Default, variant.source.clone())];

    let wd = typed.wd_lemma();
    if !is_trivial(&wd) {
        po.create_po(ProofObligation {
            name: variant_po_name(&label, "VWD"),
            nature: Nature::VariantWellDefinedness,
            global_hypotheses: po.set_handle(ALL_HYP_NAME),
            local_hypotheses: Vec::new(),
            goal: PogPredicate::new(wd, variant.source.clone()),
            sources: sources.clone(),
            hints: Vec::new(),
            accurate: machine.accurate,
        });
    }

    if let Some(ty) = typed.ty()
        && must_prove_finite(ty)
    {
        let finite = typed.factory().simple_predicate(typed.clone(), None);
        po.create_po(ProofObligation {
            name: variant_po_name(&label, "FIN"),
            nature: Nature::VariantFiniteness,
            global_hypotheses: po.set_handle(ALL_HYP_NAME),
            local_hypotheses: Vec::new(),
            goal: PogPredicate::new(finite, variant.source.clone()),
            sources,
            hints: Vec::new(),
            accurate: machine.accurate,
        });
    }
}

/// A single variant with the default label omits the label segment.
fn variant_po_name(label: &str, suffix: &str) -> String {
    if label == "vrn" {
        suffix.to_string()
    } else {
        format!("{label}/{suffix}")
    }
}

/// An integer variant decreases, so it needs no finiteness proof; a
/// set variant does, unless its type is finite by construction.
fn must_prove_finite(ty: &Type) -> bool {
    !matches!(ty, Type::Int) && !is_finite_type(ty)
}

fn is_finite_type(ty: &Type) -> bool {
    match ty {
        Type::Bool => true,
        // A given set can be infinite; ℤ is; a parametric type can be
        // (e.g. List(BOOL)).
        Type::Int | Type::Given(_) | Type::Parametric { .. } => false,
        Type::Pow(inner) => is_finite_type(inner),
        Type::Prod(left, right) => is_finite_type(left) && is_finite_type(right),
    }
}

/// The checked-file internal names of the machine's own invariants —
/// the tail of the rendered invariant closure, in declaration order.
fn own_invariant_internal_names(machine: &CheckedMachine) -> Vec<String> {
    let own = machine.record.invariants.len();
    let elems = &machine.invariant_elems;
    elems[elems.len().saturating_sub(own)..]
        .iter()
        .map(|element| {
            element
                .attr_value(attr::NAME)
                .unwrap_or_default()
                .to_string()
        })
        .collect()
}

//! Event-scoped proof obligations.
//!
//! Every event owns a hypothesis chain plugged into the machine's:
//! rooted at the machine's full hypothesis (`CTXHYP` for
//! INITIALISATION, which may not assume the invariants it must
//! establish), an identifier set with the event's parameters and the
//! primed after-values of every assigned variable, and the effective
//! guards as the incremental table.

use std::rc::Rc;

use rossi::formula::FormulaFactory;

use crate::sc::machine_record::EventDecl;
use crate::sc::{CheckedMachine, ScModel};

use super::hyp::{ALL_HYP_NAME, CTX_HYP_NAME, HypothesisManager, HypothesisRow};
use super::model::{Hint, PoFile, PogPredicate, PogSource, ProofObligation, Role, is_trivial};
use super::natures::Nature;
use super::tables::{
    AbstractEventActionTable, AbstractEventGuardList, ConcreteEventActionTable,
    ConcreteEventGuardTable, EventWitnessTable, MachineVariables, apply, assigned_variables,
    merge_batches,
};

/// Everything the event-scoped modules consume.
pub(super) struct EventScope<'a> {
    pub event: &'a Rc<EventDecl>,
    pub is_initialisation: bool,
    /// Whether the machine itself refines nothing.
    pub is_initial_machine: bool,
    pub accurate: bool,
    pub manager: HypothesisManager,
    pub guards: ConcreteEventGuardTable,
    pub abstract_events: AbstractEventGuardList,
    pub concrete_actions: ConcreteEventActionTable,
    pub abstract_actions: AbstractEventActionTable,
    pub witnesses: EventWitnessTable,
    pub variables: &'a MachineVariables,
}

impl<'a> EventScope<'a> {
    pub fn new(
        model: &ScModel,
        machine: &CheckedMachine,
        variables: &'a MachineVariables,
        event: &'a Rc<EventDecl>,
        ff: &FormulaFactory,
    ) -> Self {
        let internal_name = machine
            .event_internal_name(&event.label)
            .unwrap_or(&event.label)
            .to_string();
        let is_initialisation = event.label == crate::sc::initialisation_label();

        let guards = ConcreteEventGuardTable::new(machine, event);
        let abstract_events = AbstractEventGuardList::new(model, machine, event, &guards);

        let mut accurate = machine.accurate && event.accurate;
        for abstract_event in &abstract_events.events {
            accurate &= abstract_event.accurate;
        }

        let rows: Vec<HypothesisRow> = guards
            .guards
            .iter()
            .map(|guard| HypothesisRow {
                internal_name: guard.internal_name.clone(),
                predicate: guard.predicate.clone(),
                source: guard.source.clone(),
            })
            .collect();
        let root = if is_initialisation {
            CTX_HYP_NAME
        } else {
            ALL_HYP_NAME
        };
        let mut manager = HypothesisManager::new(
            root,
            format!("EVTIDENT{internal_name}"),
            format!("EVTHYP{internal_name}"),
            format!("EVTALLHYP{internal_name}"),
            rows,
        );

        // The event's identifiers: its own parameters, the abstract
        // events' parameters, then the primed after-values of every
        // variable assigned by the concrete or abstract event, and of
        // every primed identifier a witness mentions.
        for parameter in event.chain_parameters() {
            manager.add_identifier(parameter.name.clone(), parameter.ty.clone());
        }
        for abstract_event in &abstract_events.events {
            for parameter in abstract_event.chain_parameters() {
                manager.add_identifier(parameter.name.clone(), parameter.ty.clone());
            }
        }

        for name in assigned_variables(&event.actions) {
            if let Some(ty) = variables.types.get(&name) {
                manager.add_identifier(format!("{name}'"), ty.clone());
            }
        }
        if let Some(abstract_event) = abstract_events.first_abstract_event() {
            for name in assigned_variables(&abstract_event.actions) {
                if let Some(ty) = variables.types.get(&name) {
                    manager.add_identifier(format!("{name}'"), ty.clone());
                }
            }
        }
        for witness in &event.witnesses {
            for name in witness.typed.free_identifiers() {
                if let Some(base) = name.strip_suffix('\'')
                    && let Some(ty) = variables.types.get(base)
                {
                    manager.add_identifier(name.clone(), ty.clone());
                }
            }
        }

        let concrete_actions = ConcreteEventActionTable::new(&event.actions, variables, ff);
        let abstract_actions = match abstract_events.first_abstract_event() {
            Some(abstract_event) => {
                AbstractEventActionTable::new(&abstract_event.actions, variables, &concrete_actions)
            }
            None => AbstractEventActionTable::new(&[], variables, &concrete_actions),
        };
        let witnesses = EventWitnessTable::new(event, variables, ff);

        EventScope {
            event,
            is_initialisation,
            is_initial_machine: machine.record.refines.is_none(),
            accurate,
            manager,
            guards,
            abstract_events,
            concrete_actions,
            abstract_actions,
            witnesses,
            variables,
        }
    }

    /// The interval hint selecting the event's local hypothesis chain
    /// up to the sequent's own hypotheses.
    fn local_hypothesis_hint(&self, po: &PoFile, sequent_name: &str) -> Hint {
        Hint::Interval {
            start: po.set_handle(self.manager.root_hypothesis()),
            end: po.sequent_hypothesis_handle(sequent_name),
        }
    }
}

/// Generate every obligation of one event, then materialize its
/// hypothesis chain.
pub(super) fn generate_event(
    po: &mut PoFile,
    scope: &mut EventScope<'_>,
    machine_manager: &HypothesisManager,
    invariants: &[crate::sc::machine_record::InvariantDecl],
    variants: &[crate::sc::machine_record::VariantDecl],
) {
    guard_module(po, scope);
    witness_module(po, scope);
    invariant_module(po, scope, machine_manager, invariants);
    strengthen_guard_module(po, scope);
    action_module(po, scope);
    body_sim_module(po, scope);
    frame_sim_module(po, scope);
    variant_module(po, scope, variants);
    scope.manager.create_hypotheses(po);
}

/// Guard strengthening: the abstract guards must hold whenever the
/// concrete ones do. One `<evt>/<absGrd>/GRD` per new abstract guard
/// for a straight refinement; one disjunctive `<evt>/MRG` for an event
/// merging several abstract events.
fn strengthen_guard_module(po: &mut PoFile, scope: &mut EventScope<'_>) {
    if scope.abstract_events.refinement_type != super::tables::RefinementType::Merge {
        let Some(abstract_event) = scope.abstract_events.first_abstract_event().cloned() else {
            return;
        };
        for index in 0..scope.abstract_events.tables[0].guards.len() {
            let table = &scope.abstract_events.tables[0];
            let guard = &table.guards[index];
            if guard.is_theorem
                || is_trivial(&guard.predicate)
                || table.index_of_concrete[index].is_some()
            {
                continue;
            }
            let label = guard.label.clone();
            let guard_source = guard.source.clone();
            let goal = strengthen_substitution(scope, &guard.predicate);
            let hyp = action_and_witness_hypothesis(scope, &goal);
            let name = format!("{}/{label}/GRD", scope.event.label);
            let hints = vec![scope.local_hypothesis_hint(po, &name)];
            po.create_po(ProofObligation {
                name,
                nature: Nature::GuardStrengtheningSplit,
                global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
                local_hypotheses: hyp,
                goal: PogPredicate::new(goal, guard_source.clone()),
                sources: vec![
                    PogSource::new(Role::Abstract, abstract_event.source.clone()),
                    PogSource::new(Role::Abstract, guard_source),
                    PogSource::new(Role::Concrete, scope.event.source.clone()),
                ],
                hints,
                accurate: scope.accurate,
            });
        }
    } else {
        merge_guard_po(po, scope);
    }
}

/// The merged guard-strengthening obligation: a disjunction over the
/// abstract events of the conjunction of their new, non-theorem
/// guards. A branch with no remaining guards is trivially true and
/// discharges the whole obligation.
fn merge_guard_po(po: &mut PoFile, scope: &mut EventScope<'_>) {
    let mut disjuncts = Vec::new();
    for table in &scope.abstract_events.tables {
        if table.guards.is_empty() {
            return;
        }
        let conjuncts: Vec<rossi::formula::Predicate> = table
            .guards
            .iter()
            .enumerate()
            .filter(|(index, guard)| {
                !guard.is_theorem
                    && !is_trivial(&guard.predicate)
                    && table.index_of_concrete[*index].is_none()
            })
            .map(|(_, guard)| guard.predicate.clone())
            .collect();
        match conjuncts.len() {
            0 => return,
            1 => disjuncts.push(conjuncts.into_iter().next().expect("one conjunct")),
            _ => {
                let ff = conjuncts[0].factory().clone();
                disjuncts.push(ff.associative_predicate(
                    rossi::formula::tag::AssocPredOp::LAnd,
                    conjuncts,
                    None,
                ));
            }
        }
    }
    let ff = disjuncts[0].factory().clone();
    let disjunction =
        ff.associative_predicate(rossi::formula::tag::AssocPredOp::LOr, disjuncts, None);
    let goal = strengthen_substitution(scope, &disjunction);
    let hyp = action_and_witness_hypothesis(scope, &goal);
    let name = format!("{}/MRG", scope.event.label);
    let hints = vec![scope.local_hypothesis_hint(po, &name)];
    let mut sources: Vec<PogSource> = scope
        .abstract_events
        .events
        .iter()
        .map(|abstract_event| PogSource::new(Role::Abstract, abstract_event.source.clone()))
        .collect();
    sources.push(PogSource::new(Role::Concrete, scope.event.source.clone()));
    po.create_po(ProofObligation {
        name,
        nature: Nature::GuardStrengtheningMerge,
        global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
        local_hypotheses: hyp,
        goal: PogPredicate::new(goal, scope.event.source.clone()),
        sources,
        hints,
        accurate: scope.accurate,
    });
}

/// The guard-strengthening substitution: deterministic parameter
/// witnesses, then the frame unpriming with the deterministic
/// after-values.
fn strengthen_substitution(
    scope: &EventScope<'_>,
    predicate: &rossi::formula::Predicate,
) -> rossi::formula::Predicate {
    let goal = apply(predicate, scope.witnesses.event_det.as_ref());
    let batch = merge_batches([
        scope.concrete_actions.xi_unprime.as_ref(),
        scope.concrete_actions.table.primed_det.as_ref(),
    ]);
    apply(&goal, batch.as_ref())
}

/// `<evt>/<absAct>/SIM` — the concrete event simulates each abstract
/// assignment over the surviving variables, unless the identical
/// action also exists concretely. The goal is the abstract before-
/// after predicate carried into the concrete after-state through the
/// witnesses.
fn body_sim_module(po: &mut PoFile, scope: &mut EventScope<'_>) {
    let Some(abstract_event) = scope.abstract_events.first_abstract_event().cloned() else {
        return;
    };
    for index in 0..scope.abstract_actions.sim.len() {
        if scope
            .abstract_actions
            .index_of_concrete
            .get(index)
            .copied()
            .flatten()
            .is_some()
        {
            continue;
        }
        let sim = &scope.abstract_actions.sim[index];
        let label = sim.label.clone();
        let action_source = sim.source.clone();
        let goal = sim.assignment.ba_predicate();
        let name = format!("{}/{label}/SIM", scope.event.label);
        if is_trivial(&goal) {
            continue;
        }
        let first = merge_batches([
            scope.witnesses.machine_primed_det.as_ref(),
            scope.witnesses.event_det.as_ref(),
        ]);
        let goal = apply(&goal, first.as_ref());
        let second = merge_batches([
            scope.concrete_actions.xi_unprime.as_ref(),
            scope.concrete_actions.table.primed_det.as_ref(),
        ]);
        let goal = apply(&goal, second.as_ref());
        let hyp = action_and_witness_hypothesis(scope, &goal);
        let hints = vec![scope.local_hypothesis_hint(po, &name)];
        po.create_po(ProofObligation {
            name,
            nature: Nature::ActionSimulation,
            global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
            local_hypotheses: hyp,
            goal: PogPredicate::new(goal, action_source.clone()),
            sources: vec![
                PogSource::new(Role::Abstract, abstract_event.source.clone()),
                PogSource::new(Role::Abstract, action_source),
                PogSource::new(Role::Concrete, scope.event.source.clone()),
            ],
            hints,
            accurate: scope.accurate,
        });
    }
}

/// `<evt>/<var>/EQL` — a preserved variable the abstract event leaves
/// alone must not change: `v' = v`, with the assigning concrete
/// action's after-value substituted (deterministic) or its
/// before-after predicate assumed (nondeterministic).
fn frame_sim_module(po: &mut PoFile, scope: &mut EventScope<'_>) {
    if scope.is_initial_machine {
        return;
    }
    let abstract_event = scope.abstract_events.first_abstract_event().cloned();
    for (name, ty, preserved) in scope.variables.rows.clone() {
        if !preserved
            || scope
                .abstract_actions
                .table
                .assigned_variables
                .contains(&name)
        {
            continue;
        }
        let Some(index) = scope
            .concrete_actions
            .table
            .actions
            .iter()
            .position(|action| {
                action.assignment.assigned_identifiers().iter().any(|i| {
                    matches!(i.kind(),
                        rossi::formula::ExpressionKind::FreeIdentifier(n) if *n == name)
                })
            })
        else {
            continue;
        };

        let action = &scope.concrete_actions.table.actions[index];
        let ff = action.assignment.factory();
        let goal = ff.relational_predicate(
            rossi::formula::tag::RelationalOp::Equal,
            super::tables::primed(ff, &name, &ty),
            ff.free_identifier(&name, None, Some(ty.clone())),
            None,
        );
        let (goal, hyp) = if scope.concrete_actions.table.nondet.contains(&index) {
            let position = scope
                .concrete_actions
                .table
                .nondet
                .iter()
                .position(|i| *i == index)
                .expect("index is in the nondeterministic list");
            let ba = scope.concrete_actions.table.nondet_predicates[position].clone();
            (goal, vec![PogPredicate::new(ba, action.source.clone())])
        } else {
            (
                apply(&goal, scope.concrete_actions.table.primed_det.as_ref()),
                Vec::new(),
            )
        };

        let mut sources = Vec::new();
        if let Some(abstract_event) = &abstract_event {
            sources.push(PogSource::new(
                Role::Abstract,
                abstract_event.source.clone(),
            ));
        }
        sources.push(PogSource::new(Role::Concrete, scope.event.source.clone()));

        let sequent_name = format!("{}/{name}/EQL", scope.event.label);
        let hints = vec![scope.local_hypothesis_hint(po, &sequent_name)];
        let action_source = action.source.clone();
        po.create_po(ProofObligation {
            name: sequent_name,
            nature: Nature::CommonVariableEquality,
            global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
            local_hypotheses: hyp,
            goal: PogPredicate::new(goal, action_source),
            sources,
            hints,
            accurate: scope.accurate,
        });
    }
}

/// `<evt>/<w>/WWD` — well-definedness of every witness — and
/// `<evt>/<w>/WFIS` — feasibility of the nondeterministic ones, the
/// witness predicate with the witnessed identifier existentially
/// bound. Goals are carried into the after-state: unassigned frame
/// variables unprime and deterministic after-values substitute in.
fn witness_module(po: &mut PoFile, scope: &mut EventScope<'_>) {
    for index in 0..scope.witnesses.witnesses.len() {
        let witness = &scope.witnesses.witnesses[index];
        let label = witness.label.clone();
        let source = witness.source.clone();
        let predicate = witness.predicate.clone();
        let deterministic = witness.deterministic;

        witness_po(po, scope, &label, "WWD", predicate.wd_lemma(), &source);

        if !is_trivial(&predicate) && !deterministic {
            let fis = if predicate.free_identifiers().contains(&label) {
                let ty = scope.manager.identifier_type(&label).cloned();
                let bound = predicate.bind_idents(&[&label]);
                let decl = predicate.factory().bound_ident_decl(&label, None, None, ty);
                predicate.factory().quantified_predicate(
                    rossi::formula::tag::QuantPredOp::Exists,
                    vec![decl],
                    bound,
                    None,
                )
            } else {
                predicate.clone()
            };
            witness_po(po, scope, &label, "WFIS", fis, &source);
        }
    }
}

/// One witness obligation, with the after-state substitution and the
/// action hypotheses.
fn witness_po(
    po: &mut PoFile,
    scope: &mut EventScope<'_>,
    label: &str,
    suffix: &str,
    goal: rossi::formula::Predicate,
    source: &crate::handles::HandleUri,
) {
    let name = format!("{}/{label}/{suffix}", scope.event.label);
    if is_trivial(&goal) {
        return;
    }
    let batch = merge_batches([
        scope.concrete_actions.xi_unprime.as_ref(),
        scope.concrete_actions.table.primed_det.as_ref(),
    ]);
    let goal = apply(&goal, batch.as_ref());
    let hyp = action_hypothesis(scope, &goal);
    let nature = if suffix == "WWD" {
        Nature::WitnessWellDefinedness
    } else {
        Nature::WitnessFeasibility
    };
    let hints = vec![scope.local_hypothesis_hint(po, &name)];
    po.create_po(ProofObligation {
        name,
        nature,
        global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
        local_hypotheses: hyp,
        goal: PogPredicate::new(goal, source.clone()),
        sources: vec![PogSource::new(Role::Default, source.clone())],
        hints,
        accurate: scope.accurate,
    });
}

/// `<evt>/<act>/WD` and `<evt>/<act>/FIS` for the event's actions.
///
/// An action identical to an abstract one was already proved there:
/// it gets no obligations, except that its feasibility is still due
/// when the abstract hypotheses could not be assumed.
fn action_module(po: &mut PoFile, scope: &mut EventScope<'_>) {
    if scope.concrete_actions.table.actions.is_empty() {
        return;
    }
    let hints = vec![Hint::Interval {
        start: po.set_handle(scope.manager.root_hypothesis()),
        end: po.set_handle(scope.manager.full_hypothesis()),
    }];
    let abstract_hyp = abstract_action_hypothesis(scope);

    for k in 0..scope.concrete_actions.table.actions.len() {
        let action = &scope.concrete_actions.table.actions[k];
        let label = action.label.clone();
        let source = action.source.clone();
        let assignment = action.assignment.clone();
        let sources = vec![PogSource::new(Role::Default, source.clone())];
        let hyp = abstract_hyp.clone();
        let not_same_as_abstract = scope.abstract_actions.index_of_abstract[k].is_none();

        if not_same_as_abstract {
            po.create_po(ProofObligation {
                name: format!("{}/{label}/WD", scope.event.label),
                nature: Nature::ActionWellDefinedness,
                global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
                local_hypotheses: hyp.clone(),
                goal: PogPredicate::new(assignment.wd_lemma(), source.clone()),
                sources: sources.clone(),
                hints: hints.clone(),
                accurate: scope.accurate,
            });
        }

        if hyp.is_empty() || not_same_as_abstract {
            po.create_po(ProofObligation {
                name: format!("{}/{label}/FIS", scope.event.label),
                nature: Nature::ActionFeasibility,
                global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
                local_hypotheses: hyp,
                goal: PogPredicate::new(assignment.fis_predicate(), source),
                sources,
                hints: hints.clone(),
                accurate: scope.accurate,
            });
        }
    }
}

/// The abstract event's nondeterministic before-after predicates as
/// local hypotheses for the concrete action obligations, preceded by
/// the nondeterministic parameter-witness predicates. Bails out to no
/// hypotheses at all when a parameter witness mentions a primed
/// identifier — the after-state cannot be assumed there.
fn abstract_action_hypothesis(scope: &EventScope<'_>) -> Vec<PogPredicate> {
    let mut hyp = Vec::new();
    for witness in &scope.witnesses.witnesses {
        if witness.label.ends_with('\'') {
            continue;
        }
        if witness
            .predicate
            .free_identifiers()
            .iter()
            .any(|name| name.ends_with('\''))
        {
            return Vec::new();
        }
        if !witness.deterministic {
            hyp.push(PogPredicate::new(
                witness.predicate.clone(),
                witness.source.clone(),
            ));
        }
    }

    let table = &scope.abstract_actions.table;
    for (index, ba) in table.nondet.iter().zip(&table.nondet_predicates) {
        let predicate = apply(ba, scope.witnesses.event_det.as_ref());
        hyp.push(PogPredicate::new(
            predicate,
            table.actions[*index].source.clone(),
        ));
    }
    hyp
}

/// `<evt>/<inv>/INV` — invariant establishment (INITIALISATION) or
/// preservation. The invariant must mention a variable the concrete
/// or abstract event assigns, unless the event is the INITIALISATION,
/// which establishes every invariant.
fn invariant_module(
    po: &mut PoFile,
    scope: &mut EventScope<'_>,
    machine_manager: &HypothesisManager,
    invariants: &[crate::sc::machine_record::InvariantDecl],
) {
    let refines = !scope.abstract_events.events.is_empty();
    for (index, invariant) in invariants.iter().enumerate() {
        if invariant.is_theorem || is_trivial(&invariant.typed) {
            continue;
        }
        let mentions_assigned = invariant.typed.free_identifiers().iter().any(|name| {
            scope
                .concrete_actions
                .table
                .assigned_variables
                .contains(name)
                || scope
                    .abstract_actions
                    .table
                    .assigned_variables
                    .contains(name)
        });
        if !mentions_assigned && !scope.is_initialisation {
            continue;
        }

        let (goal, hyp, sources) = if refines {
            refined_invariant_goal(scope, invariant)
        } else {
            let goal = apply(
                &apply(
                    &invariant.typed,
                    scope.concrete_actions.delta_prime.as_ref(),
                ),
                scope.concrete_actions.table.primed_det.as_ref(),
            );
            let hyp = action_hypothesis(scope, &goal);
            let sources = vec![
                PogSource::new(Role::Default, scope.event.source.clone()),
                PogSource::new(Role::Default, invariant.source.clone()),
            ];
            (goal, hyp, sources)
        };

        let name = format!("{}/{}/INV", scope.event.label, invariant.label);
        let (set_name, predicate_name) = machine_manager.predicate_location(index);
        let hints = vec![
            scope.local_hypothesis_hint(po, &name),
            Hint::Predicate(po.predicate_handle(&set_name, &predicate_name)),
        ];
        po.create_po(ProofObligation {
            name,
            nature: if scope.is_initialisation {
                Nature::InvariantEstablishment
            } else {
                Nature::InvariantPreservation
            },
            global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
            local_hypotheses: hyp,
            goal: PogPredicate::new(goal, invariant.source.clone()),
            sources,
            hints,
            accurate: scope.accurate,
        });
    }
}

/// The refined-event invariant goal: the abstract state is expressed
/// through the witnesses, then the concrete after-state substitutes
/// in. Three sequential batches:
///
/// 1. assigned variables prime (`v ↦ v'`), deterministic machine
///    witnesses and the nondeterministic prime renaming replace the
///    dropped abstract variables, and deterministic abstract
///    assignments to dropped variables act as implicit witnesses;
/// 2. deterministic parameter witnesses replace the dropped abstract
///    parameters;
/// 3. the unassigned frame unprimes (`v' ↦ v`) and deterministic
///    after-values substitute in (`x' ↦ E`).
fn refined_invariant_goal(
    scope: &EventScope<'_>,
    invariant: &crate::sc::machine_record::InvariantDecl,
) -> (rossi::formula::Predicate, Vec<PogPredicate>, Vec<PogSource>) {
    let first = merge_batches([
        scope.concrete_actions.delta_prime.as_ref(),
        scope.witnesses.machine_det.as_ref(),
        scope.witnesses.prime_substitution.as_ref(),
        scope.abstract_actions.disappearing_witnesses.as_ref(),
    ]);
    let goal = apply(&invariant.typed, first.as_ref());
    let goal = apply(&goal, scope.witnesses.event_det.as_ref());
    let third = merge_batches([
        scope.concrete_actions.xi_unprime.as_ref(),
        scope.concrete_actions.table.primed_det.as_ref(),
    ]);
    let goal = apply(&goal, third.as_ref());

    let hyp = action_and_witness_hypothesis(scope, &goal);
    let abstract_event = scope
        .abstract_events
        .first_abstract_event()
        .expect("refined events have an abstract event");
    let sources = vec![
        PogSource::new(Role::Abstract, abstract_event.source.clone()),
        PogSource::new(Role::Concrete, scope.event.source.clone()),
        PogSource::new(Role::Default, invariant.source.clone()),
    ];
    (goal, hyp, sources)
}

/// The witness hypotheses whose witnessed identifier occurs in the
/// goal (carried into the after-state), the identifiers they
/// introduce, then the action hypotheses over the grown set.
fn action_and_witness_hypothesis(
    scope: &EventScope<'_>,
    goal: &rossi::formula::Predicate,
) -> Vec<PogPredicate> {
    let mut free: std::collections::HashSet<String> =
        goal.free_identifiers().iter().cloned().collect();

    let batch = merge_batches([
        scope.concrete_actions.table.primed_det.as_ref(),
        scope.concrete_actions.xi_unprime.as_ref(),
    ]);
    let mut hyp = Vec::new();
    for index in &scope.witnesses.nondet {
        let witness = &scope.witnesses.witnesses[*index];
        if free.contains(&witness.label) {
            let predicate = apply(&witness.predicate, batch.as_ref());
            hyp.push(PogPredicate::new(predicate, witness.source.clone()));
        }
    }
    for predicate in hyp.clone() {
        for name in predicate.predicate.free_identifiers() {
            free.insert(name.clone());
        }
    }

    let table = &scope.concrete_actions.table;
    for (index, ba) in table.nondet.iter().zip(&table.nondet_predicates) {
        if ba
            .free_identifiers()
            .iter()
            .any(|name| name.ends_with('\'') && free.contains(name))
        {
            hyp.push(PogPredicate::new(
                ba.clone(),
                table.actions[*index].source.clone(),
            ));
        }
    }
    hyp
}

/// The concrete nondeterministic before-after predicates whose primed
/// identifiers occur in the goal, as local hypotheses.
fn action_hypothesis(
    scope: &EventScope<'_>,
    goal: &rossi::formula::Predicate,
) -> Vec<PogPredicate> {
    let free: std::collections::HashSet<&str> =
        goal.free_identifiers().iter().map(String::as_str).collect();
    let table = &scope.concrete_actions.table;
    table
        .nondet
        .iter()
        .zip(&table.nondet_predicates)
        .filter(|(_, ba)| {
            ba.free_identifiers()
                .iter()
                .any(|name| name.ends_with('\'') && free.contains(name.as_str()))
        })
        .map(|(index, ba)| PogPredicate::new(ba.clone(), table.actions[*index].source.clone()))
        .collect()
}

/// `<evt>/<grd>/WD` for every effective guard with a non-trivial
/// well-definedness lemma, and `<evt>/<grd>/THM` for guard theorems —
/// unless the identical guard was already proved for every abstract
/// event at a compatible position.
fn guard_module(po: &mut PoFile, scope: &mut EventScope<'_>) {
    for index in 0..scope.guards.guards.len() {
        let guard = &scope.guards.guards[index];
        let label = guard.label.clone();
        let predicate = guard.predicate.clone();
        let source = guard.source.clone();
        let is_theorem = guard.is_theorem;

        let wd = predicate.wd_lemma();
        if !is_trivial(&wd) && !is_redundant(scope, index, false) {
            let hypothesis = scope.manager.make_hypothesis(index);
            po.create_po(ProofObligation {
                name: format!("{}/{label}/WD", scope.event.label),
                nature: if is_theorem {
                    Nature::TheoremWellDefinedness
                } else {
                    Nature::GuardWellDefinedness
                },
                global_hypotheses: po.set_handle(&hypothesis),
                local_hypotheses: Vec::new(),
                goal: PogPredicate::new(wd, source.clone()),
                sources: vec![PogSource::new(Role::Default, source.clone())],
                hints: vec![Hint::Interval {
                    start: po.set_handle(scope.manager.root_hypothesis()),
                    end: po.set_handle(&hypothesis),
                }],
                accurate: scope.accurate,
            });
        }

        if is_theorem && !is_trivial(&predicate) && !is_redundant(scope, index, true) {
            let hypothesis = scope.manager.make_hypothesis(index);
            po.create_po(ProofObligation {
                name: format!("{}/{label}/THM", scope.event.label),
                nature: Nature::Theorem,
                global_hypotheses: po.set_handle(&hypothesis),
                local_hypotheses: Vec::new(),
                goal: PogPredicate::new(predicate, source.clone()),
                sources: vec![PogSource::new(Role::Default, source)],
                hints: vec![Hint::Interval {
                    start: po.set_handle(scope.manager.root_hypothesis()),
                    end: po.set_handle(&hypothesis),
                }],
                accurate: scope.accurate,
            });
        }
    }
}

/// A guard obligation is redundant when some abstract event already
/// carries the identical guard at a compatible position: every
/// abstract guard before it must correspond to a concrete guard
/// declared before this one.
fn is_redundant(scope: &EventScope<'_>, index: usize, is_theorem: bool) -> bool {
    let predicate = &scope.guards.guards[index].predicate;
    scope.abstract_events.tables.iter().any(|table| {
        let Some(abs_index) = table.guards.iter().position(|g| g.predicate == *predicate) else {
            return false;
        };
        if is_theorem && !table.guards[abs_index].is_theorem {
            return false;
        }
        (0..abs_index).all(|k| {
            table.index_of_concrete[k].is_some_and(|concrete_index| concrete_index < index)
        })
    })
}

/// `<evt>/NAT` and `<evt>/VAR` — the variants form a lexicographic
/// order: every modified variant but the last must not increase, the
/// last one strictly decreases when the event is convergent, and each
/// obligation assumes the earlier variants unchanged. No obligation
/// for ordinary events, for convergent events refining convergent
/// abstractions (proved there), or for anticipated events of machines
/// without a variant.
pub(super) fn variant_module(
    po: &mut PoFile,
    scope: &mut EventScope<'_>,
    variants: &[crate::sc::machine_record::VariantDecl],
) {
    use crate::sc::machine_record::Convergence;
    let convergence = scope.event.convergence;
    if convergence == Convergence::Ordinary {
        return;
    }
    let abstract_convergent = !scope.abstract_events.events.is_empty()
        && scope
            .abstract_events
            .events
            .iter()
            .all(|e| e.convergence == Convergence::Convergent);
    if convergence == Convergence::Convergent && abstract_convergent {
        return;
    }
    let is_convergent = convergence == Convergence::Convergent;

    // The participating variants: those the event modifies. An untouched
    // variant obliges nothing — except that a convergent event modifying
    // none must still strictly decrease the last variant (an unprovable
    // goal that correctly flags the model).
    struct Info<'a> {
        variant: &'a crate::sc::machine_record::VariantDecl,
        expression: &'a rossi::formula::Expression,
        next: rossi::formula::Expression,
        is_natural: bool,
    }
    let mut infos: Vec<Info<'_>> = Vec::new();
    let mut untouched_last: Option<Info<'_>> = None;
    for variant in variants {
        let Some(expression) = &variant.typed else {
            continue;
        };
        let info = Info {
            variant,
            expression,
            next: after_expression(scope, expression),
            is_natural: matches!(expression.ty(), Some(rossi::formula::Type::Int)),
        };
        if info.next != *info.expression {
            infos.push(info);
        } else {
            untouched_last = Some(info);
        }
    }
    if is_convergent && infos.is_empty() {
        match untouched_last {
            Some(info) => infos.push(info),
            None => return,
        }
    }

    // One NAT/VAR pair per participant, under an accumulator: the
    // sources of the variants so far, the equality hypotheses assuming
    // the earlier variants unchanged, and the before-after predicates
    // for the primed identifiers the goals introduced.
    let single_default = variants.len() == 1 && variants[0].label == "vrn";
    let mut sources = vec![PogSource::new(Role::Default, scope.event.source.clone())];
    let mut hyps: Vec<PogPredicate> = Vec::new();
    let mut covered: std::collections::HashSet<String> = std::collections::HashSet::new();
    let count = infos.len();
    for (i, info) in infos.iter().enumerate() {
        let is_last = i + 1 == count;
        let ff = info.expression.factory();
        sources.push(PogSource::new(Role::Default, info.variant.source.clone()));

        if info.is_natural && (is_convergent || !is_last) {
            let natural = ff.atomic_expression(
                rossi::formula::tag::AtomicOp::Natural,
                None,
                Some(rossi::formula::Type::pow(rossi::formula::Type::Int)),
            );
            let goal = ff.relational_predicate(
                rossi::formula::tag::RelationalOp::In,
                info.expression.clone(),
                natural,
                None,
            );
            let name = variant_event_po_name(
                &scope.event.label,
                single_default,
                &info.variant.label,
                "NAT",
            );
            let hints = vec![scope.local_hypothesis_hint(po, &name)];
            po.create_po(ProofObligation {
                name,
                nature: Nature::EventNaturalNumberVariant,
                global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
                local_hypotheses: hyps.clone(),
                goal: PogPredicate::new(goal, info.variant.source.clone()),
                sources: sources.clone(),
                hints,
                accurate: scope.accurate,
            });
        }

        let op = match (info.is_natural, is_convergent && is_last) {
            (true, true) => rossi::formula::tag::RelationalOp::Lt,
            (true, false) => rossi::formula::tag::RelationalOp::Le,
            (false, true) => rossi::formula::tag::RelationalOp::Subset,
            (false, false) => rossi::formula::tag::RelationalOp::SubsetEq,
        };
        let goal = ff.relational_predicate(op, info.next.clone(), info.expression.clone(), None);
        incremental_action_hypothesis(scope, &goal, &mut hyps, &mut covered);
        let name = variant_event_po_name(
            &scope.event.label,
            single_default,
            &info.variant.label,
            "VAR",
        );
        let hints = vec![scope.local_hypothesis_hint(po, &name)];
        po.create_po(ProofObligation {
            name,
            nature: Nature::EventVariant,
            global_hypotheses: po.set_handle(scope.manager.full_hypothesis()),
            local_hypotheses: hyps.clone(),
            goal: PogPredicate::new(goal, info.variant.source.clone()),
            sources: sources.clone(),
            hints,
            accurate: scope.accurate,
        });

        if !is_last {
            let eq = ff.relational_predicate(
                rossi::formula::tag::RelationalOp::Equal,
                info.next.clone(),
                info.expression.clone(),
                None,
            );
            hyps.push(PogPredicate::new(eq, info.variant.source.clone()));
        }
    }
}

/// Extend the accumulated hypotheses with the concrete nondeterministic
/// before-after predicates for the goal's primed identifiers not covered
/// yet, recording the goal's identifiers as covered.
fn incremental_action_hypothesis(
    scope: &EventScope<'_>,
    goal: &rossi::formula::Predicate,
    hyps: &mut Vec<PogPredicate>,
    covered: &mut std::collections::HashSet<String>,
) {
    let new_idents: Vec<String> = goal
        .free_identifiers()
        .iter()
        .filter(|name| !covered.contains(*name))
        .cloned()
        .collect();
    let table = &scope.concrete_actions.table;
    for (index, ba) in table.nondet.iter().zip(&table.nondet_predicates) {
        if ba
            .free_identifiers()
            .iter()
            .any(|name| name.ends_with('\'') && new_idents.contains(name))
        {
            hyps.push(PogPredicate::new(
                ba.clone(),
                table.actions[*index].source.clone(),
            ));
        }
    }
    covered.extend(new_idents);
}

/// The variant's value after the event: assigned variables prime and
/// deterministic after-values substitute in.
fn after_expression(
    scope: &EventScope<'_>,
    expression: &rossi::formula::Expression,
) -> rossi::formula::Expression {
    let mut next = expression.clone();
    if let Some(delta) = scope.concrete_actions.delta_prime.as_ref() {
        next = next.substitute_free_idents(delta);
    }
    if let Some(primed_det) = scope.concrete_actions.table.primed_det.as_ref() {
        next = next.substitute_free_idents(primed_det);
    }
    next
}

/// A machine whose only variant carries the default label omits the
/// label segment; every other shape includes it.
fn variant_event_po_name(
    event_label: &str,
    single_default: bool,
    label: &str,
    suffix: &str,
) -> String {
    if single_default {
        format!("{event_label}/{suffix}")
    } else {
        format!("{event_label}/{label}/{suffix}")
    }
}

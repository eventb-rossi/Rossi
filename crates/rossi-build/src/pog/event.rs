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
    ConcreteEventGuardTable, MachineVariables, apply, assigned_variables,
};

/// Everything the event-scoped modules consume.
pub(super) struct EventScope<'a> {
    pub event: &'a Rc<EventDecl>,
    pub is_initialisation: bool,
    pub accurate: bool,
    pub manager: HypothesisManager,
    pub guards: ConcreteEventGuardTable,
    pub abstract_events: AbstractEventGuardList,
    pub concrete_actions: ConcreteEventActionTable,
    pub abstract_actions: AbstractEventActionTable,
}

impl<'a> EventScope<'a> {
    pub fn new(
        model: &ScModel,
        machine: &CheckedMachine,
        variables: &MachineVariables,
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
                AbstractEventActionTable::new(&abstract_event.actions, &concrete_actions)
            }
            None => AbstractEventActionTable::new(&[], &concrete_actions),
        };

        EventScope {
            event,
            is_initialisation,
            accurate,
            manager,
            guards,
            abstract_events,
            concrete_actions,
            abstract_actions,
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
) {
    guard_module(po, scope);
    action_module(po, scope);
    new_event_invariant_module(po, scope, machine_manager, invariants);
    scope.manager.create_hypotheses(po);
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

/// The abstract event's nondeterministic before-after predicates, as
/// local hypotheses for the concrete action obligations.
fn abstract_action_hypothesis(scope: &EventScope<'_>) -> Vec<PogPredicate> {
    let table = &scope.abstract_actions.table;
    table
        .nondet
        .iter()
        .zip(&table.nondet_predicates)
        .map(|(index, ba)| PogPredicate::new(ba.clone(), table.actions[*index].source.clone()))
        .collect()
}

/// `<evt>/<inv>/INV` — invariant establishment (INITIALISATION) or
/// preservation, for events refining nothing. The invariant must
/// mention a variable the event assigns, unless the event is the
/// INITIALISATION, which establishes every invariant.
fn new_event_invariant_module(
    po: &mut PoFile,
    scope: &mut EventScope<'_>,
    machine_manager: &HypothesisManager,
    invariants: &[crate::sc::machine_record::InvariantDecl],
) {
    if !scope.abstract_events.events.is_empty() {
        return;
    }
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

        let goal = apply(
            &apply(
                &invariant.typed,
                scope.concrete_actions.delta_prime.as_ref(),
            ),
            scope.concrete_actions.table.primed_det.as_ref(),
        );
        let hyp = action_hypothesis(scope, &goal);
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
            sources: vec![
                PogSource::new(Role::Default, scope.event.source.clone()),
                PogSource::new(Role::Default, invariant.source.clone()),
            ],
            hints,
            accurate: scope.accurate,
        });
    }
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

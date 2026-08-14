//! Per-event tables: actions split by determinism with the frame
//! substitutions, guard correspondences between an event and the
//! abstract events it refines, and the machine-state lookups the
//! event scope is built from.

use std::collections::{BTreeSet, HashMap};

use rossi::formula::{Assignment, AssignmentKind, Expression, FormulaFactory, Predicate, Type};

use crate::handles::HandleUri;
use crate::sc::machine_record::{ActionDecl, EventDecl, GuardDecl, MachineRecord};
use crate::sc::{CheckedMachine, ScModel};

/// A simultaneous free-identifier substitution (one batch of parallel
/// assignments).
pub(super) type Substitution = HashMap<String, Expression>;

/// Apply an optional substitution batch.
pub(super) fn apply(predicate: &Predicate, subst: Option<&Substitution>) -> Predicate {
    match subst {
        Some(map) if !map.is_empty() => predicate.substitute_free_idents(map),
        _ => predicate.clone(),
    }
}

/// The primed after-value identifier of a variable.
pub(super) fn primed(ff: &FormulaFactory, name: &str, ty: &Type) -> Expression {
    ff.free_identifier(format!("{name}'"), None, Some(ty.clone()))
}

/// The concrete machine state: every concrete variable in declaration
/// order with whether it is preserved (also present in the
/// abstraction), plus a by-name type lookup over all visible variables
/// (abstract-only ones included) — the type source for primed
/// identifiers.
pub(super) struct MachineVariables {
    pub rows: Vec<(String, Type, bool)>,
    pub types: HashMap<String, Type>,
}

impl MachineVariables {
    pub fn new(record: &MachineRecord) -> Self {
        MachineVariables {
            rows: record
                .variables
                .iter()
                .filter(|v| v.is_concrete)
                .map(|v| (v.name.clone(), v.ty.clone(), v.is_abstract && v.is_concrete))
                .collect(),
            types: record
                .variables
                .iter()
                .map(|v| (v.name.clone(), v.ty.clone()))
                .collect(),
        }
    }
}

/// The names of every variable the actions assign.
pub(super) fn assigned_variables(actions: &[ActionDecl]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for decl in actions {
        // `skip` assigns nothing.
        let Some(assignment) = &decl.typed else {
            continue;
        };
        for ident in assignment.assigned_identifiers() {
            if let rossi::formula::ExpressionKind::FreeIdentifier(name) = ident.kind() {
                out.insert(name.clone());
            }
        }
    }
    out
}

/// One action and its typed assignment.
pub(super) struct ActionInfo {
    pub label: String,
    pub source: HandleUri,
    pub assignment: Assignment,
}

/// An event's actions, split by determinism. `skip` actions assign
/// nothing and constrain nothing, so they carry no row.
pub(super) struct EventActionTable {
    pub actions: Vec<ActionInfo>,
    /// Indices into `actions` of the nondeterministic ones, with their
    /// before-after predicates in parallel.
    pub nondet: Vec<usize>,
    pub nondet_predicates: Vec<Predicate>,
    /// `x' ↦ E` for every deterministic action, as one batch.
    pub primed_det: Option<Substitution>,
    pub assigned_variables: BTreeSet<String>,
}

impl EventActionTable {
    pub fn new(actions: &[ActionDecl]) -> Self {
        let mut table = EventActionTable {
            actions: Vec::new(),
            nondet: Vec::new(),
            nondet_predicates: Vec::new(),
            primed_det: None,
            assigned_variables: assigned_variables(actions),
        };
        let mut primed_det = Substitution::new();
        for decl in actions {
            let Some(assignment) = &decl.typed else {
                continue;
            };
            let index = table.actions.len();
            table.actions.push(ActionInfo {
                label: decl.label.clone(),
                source: decl.source.clone(),
                assignment: assignment.clone(),
            });
            match assignment.kind() {
                AssignmentKind::BecomesEqualTo { idents, values } => {
                    for (ident, value) in idents.iter().zip(values) {
                        if let rossi::formula::ExpressionKind::FreeIdentifier(name) = ident.kind() {
                            primed_det.insert(format!("{name}'"), value.clone());
                        }
                    }
                }
                AssignmentKind::BecomesMemberOf { .. } | AssignmentKind::BecomesSuchThat { .. } => {
                    table.nondet.push(index);
                    table.nondet_predicates.push(assignment.ba_predicate());
                }
            }
        }
        table.primed_det = (!primed_det.is_empty()).then_some(primed_det);
        table
    }
}

/// The concrete event's actions plus the frame substitutions over the
/// machine state.
pub(super) struct ConcreteEventActionTable {
    pub table: EventActionTable,
    /// `v ↦ v'` for every variable the event assigns.
    pub delta_prime: Option<Substitution>,
}

impl ConcreteEventActionTable {
    pub fn new(actions: &[ActionDecl], variables: &MachineVariables, ff: &FormulaFactory) -> Self {
        let table = EventActionTable::new(actions);
        let mut delta = Substitution::new();
        for (name, ty, _) in &variables.rows {
            if table.assigned_variables.contains(name) {
                delta.insert(name.clone(), primed(ff, name, ty));
            }
        }
        ConcreteEventActionTable {
            table,
            delta_prime: (!delta.is_empty()).then_some(delta),
        }
    }
}

/// The abstract event's actions, with the correspondence to the
/// concrete action list (structural formula equality).
pub(super) struct AbstractEventActionTable {
    pub table: EventActionTable,
    /// For each concrete action, the index of the identical abstract
    /// action, if any.
    pub index_of_abstract: Vec<Option<usize>>,
}

impl AbstractEventActionTable {
    pub fn new(actions: &[ActionDecl], concrete: &ConcreteEventActionTable) -> Self {
        let table = EventActionTable::new(actions);
        let index_of_abstract = concrete
            .table
            .actions
            .iter()
            .map(|c| {
                table
                    .actions
                    .iter()
                    .position(|a| a.assignment == c.assignment)
            })
            .collect();
        AbstractEventActionTable {
            table,
            index_of_abstract,
        }
    }
}

/// One guard of the effective (inherited-then-own) guard list.
pub(super) struct GuardInfo {
    pub label: String,
    /// The checked file's internal name of the guard row.
    pub internal_name: String,
    pub predicate: Predicate,
    pub source: HandleUri,
    pub is_theorem: bool,
}

/// The effective guards of an event, in checked-file order.
pub(super) struct ConcreteEventGuardTable {
    pub guards: Vec<GuardInfo>,
}

impl ConcreteEventGuardTable {
    pub fn new(machine: &CheckedMachine, event: &EventDecl) -> Self {
        let guards = effective_guards(event)
            .into_iter()
            .map(|guard| GuardInfo {
                label: guard.label.clone(),
                internal_name: machine
                    .event_child_internal_name(
                        &event.label,
                        crate::xml_out::tag::SC_GUARD,
                        &guard.label,
                    )
                    .unwrap_or(&guard.label)
                    .to_string(),
                predicate: guard.typed.clone(),
                source: guard.source.clone(),
                is_theorem: guard.is_theorem,
            })
            .collect();
        ConcreteEventGuardTable { guards }
    }
}

/// An abstract event's effective guards, with the correspondence to
/// the concrete guard list (structural formula equality).
pub(super) struct AbstractEventGuardTable {
    pub guards: Vec<AbstractGuardInfo>,
    /// For each abstract guard, the index of the identical concrete
    /// guard, if any.
    pub index_of_concrete: Vec<Option<usize>>,
}

pub(super) struct AbstractGuardInfo {
    pub predicate: Predicate,
    pub is_theorem: bool,
}

impl AbstractEventGuardTable {
    pub fn new(abstract_event: &EventDecl, concrete: &ConcreteEventGuardTable) -> Self {
        let guards: Vec<AbstractGuardInfo> = effective_guards(abstract_event)
            .into_iter()
            .map(|guard| AbstractGuardInfo {
                predicate: guard.typed.clone(),
                is_theorem: guard.is_theorem,
            })
            .collect();
        let index_of_concrete = guards
            .iter()
            .map(|a| {
                concrete
                    .guards
                    .iter()
                    .position(|c| c.predicate == a.predicate)
            })
            .collect();
        AbstractEventGuardTable {
            guards,
            index_of_concrete,
        }
    }
}

/// The abstract events an event refines, with their guard tables.
pub(super) struct AbstractEventGuardList {
    pub events: Vec<std::rc::Rc<EventDecl>>,
    pub tables: Vec<AbstractEventGuardTable>,
}

impl AbstractEventGuardList {
    pub fn new(
        model: &ScModel,
        machine: &CheckedMachine,
        event: &EventDecl,
        concrete: &ConcreteEventGuardTable,
    ) -> Self {
        let events: Vec<std::rc::Rc<EventDecl>> = model
            .abstract_event(machine, event)
            .cloned()
            .into_iter()
            .collect();
        let tables = events
            .iter()
            .map(|abstract_event| AbstractEventGuardTable::new(abstract_event, concrete))
            .collect();
        AbstractEventGuardList { events, tables }
    }

    pub fn first_abstract_event(&self) -> Option<&std::rc::Rc<EventDecl>> {
        self.events.first()
    }
}

/// The effective guard list: the inherited chain's guards (root
/// first), then the event's own, matching the checked file's order.
fn effective_guards(event: &EventDecl) -> Vec<&GuardDecl> {
    let mut out: Vec<&GuardDecl> = Vec::new();
    for ancestor in event.chain_root_first() {
        out.extend(ancestor.guards.iter());
    }
    out.extend(event.guards.iter());
    out
}

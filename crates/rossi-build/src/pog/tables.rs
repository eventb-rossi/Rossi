//! Per-event tables: guard correspondences between an event and the
//! abstract events it refines, and the machine-state lookups the
//! event scope is built from.

use std::collections::{BTreeSet, HashMap};

use rossi::formula::{Predicate, Type};

use crate::handles::HandleUri;
use crate::sc::machine_record::{ActionDecl, EventDecl, GuardDecl, MachineRecord};
use crate::sc::{CheckedMachine, ScModel};

/// The visible machine state, by name — the type source for primed
/// identifiers.
pub(super) struct MachineVariables {
    pub types: HashMap<String, Type>,
}

impl MachineVariables {
    pub fn new(record: &MachineRecord) -> Self {
        MachineVariables {
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

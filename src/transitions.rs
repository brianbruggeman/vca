use crate::admissibility::is_admissible;
use crate::relation::{PosIndex, Relation};
use crate::slot::SlotId;
use crate::system::{SystemError, VCASystem};
use crate::types::SlotType;

/// The 5 Δ primitives that transform a VCASystem (Theorem 8).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Transition {
    InsertSlot { v: SlotId, t: SlotType },
    DeleteSlot { v: SlotId },
    Attach { u: SlotId, v: SlotId, i: PosIndex },
    Detach { u: SlotId, v: SlotId, i: PosIndex },
    Retype { v: SlotId, t: SlotType },
}

#[derive(Debug, PartialEq, Eq)]
pub enum TransitionError {
    PreconditionFailed(String),
    SystemError(SystemError),
}

impl std::fmt::Display for TransitionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PreconditionFailed(msg) => write!(f, "precondition failed: {msg}"),
            Self::SystemError(e) => write!(f, "system error: {e:?}"),
        }
    }
}

impl std::error::Error for TransitionError {}

impl From<SystemError> for TransitionError {
    fn from(e: SystemError) -> Self {
        Self::SystemError(e)
    }
}

impl Transition {
    /// Returns true if this transition's preconditions hold in the given system.
    pub fn precondition(&self, system: &VCASystem) -> bool {
        match self {
            Transition::InsertSlot { v, t } => !system.contains_slot(*v) && t.is_well_formed(),
            Transition::DeleteSlot { v } => system.contains_slot(*v) && system.slot_count() > 1,
            Transition::Attach { u, v, i } => {
                if !system.contains_slot(*u) || !system.contains_slot(*v) {
                    return false;
                }

                let position_occupied = system
                    .relations
                    .iter()
                    .any(|rel| rel.target == *v && rel.position == *i);

                if position_occupied {
                    return false;
                }

                let relation = Relation {
                    source: *u,
                    target: *v,
                    position: *i,
                };

                if !is_admissible(system, &relation) {
                    return false;
                }

                let current_src_count = system.src_count(*v);
                let Some(slot_type) = system.type_of(*v) else {
                    return false;
                };

                slot_type.upper_satisfied(current_src_count + 1)
            }
            Transition::Detach { u, v, i } => system.relations.contains(&Relation {
                source: *u,
                target: *v,
                position: *i,
            }),
            Transition::Retype { v, t } => {
                if !system.contains_slot(*v) {
                    return false;
                }

                if !t.is_well_formed() {
                    return false;
                }

                let src_count = system.src_count(*v);
                t.upper_satisfied(src_count)
            }
        }
    }

    /// Applies this transition to produce a new system, preserving structural validity.
    pub fn apply(&self, system: &VCASystem) -> Result<VCASystem, TransitionError> {
        if !self.precondition(system) {
            return Err(TransitionError::PreconditionFailed(format!(
                "precondition failed for {:?}",
                self
            )));
        }

        match self {
            Transition::InsertSlot { v, t } => {
                let mut new_system = system.clone();
                new_system.slots.push(*v);
                new_system.types.insert(*v, t.clone());
                Ok(new_system)
            }
            Transition::DeleteSlot { v } => {
                let mut new_system = system.clone();
                new_system.slots.retain(|&slot| slot != *v);
                new_system.types.remove(v);
                new_system
                    .relations
                    .retain(|rel| rel.source != *v && rel.target != *v);
                Ok(new_system)
            }
            Transition::Attach { u, v, i } => {
                let mut new_system = system.clone();
                new_system.relations.push(Relation {
                    source: *u,
                    target: *v,
                    position: *i,
                });
                Ok(new_system)
            }
            Transition::Detach { u, v, i } => {
                let mut new_system = system.clone();
                new_system
                    .relations
                    .retain(|rel| !(rel.source == *u && rel.target == *v && rel.position == *i));
                Ok(new_system)
            }
            Transition::Retype { v, t } => {
                let mut new_system = system.clone();
                new_system.types.insert(*v, t.clone());
                Ok(new_system)
            }
        }
    }
}

/// Convenience wrapper for [`Transition::apply`].
pub fn apply_transition(
    transition: &Transition,
    system: &VCASystem,
) -> Result<VCASystem, TransitionError> {
    transition.apply(system)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::types::{Affinity, Family, Kind, Layer, TypeId, TypeMeta, UpperBound};

    fn make_test_slot() -> (SlotId, SlotType) {
        let slot = SlotId(1);
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        (slot, slot_type)
    }

    fn make_test_system() -> VCASystem {
        let (slot, slot_type) = make_test_slot();
        VCASystem::new(slot, slot_type).unwrap()
    }

    #[test]
    fn insert_slot_precondition_fails_when_v_already_in_v() {
        let system = make_test_system();
        let (slot, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: slot,
            t: slot_type,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn insert_slot_precondition_fails_when_type_not_well_formed() {
        let system = make_test_system();
        let bad_slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 10,
            upper: UpperBound::Finite(5),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let transition = Transition::InsertSlot {
            v: SlotId(999),
            t: bad_slot_type,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn insert_slot_precondition_succeeds_when_valid() {
        let system = make_test_system();
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: SlotId(999),
            t: slot_type,
        };
        assert!(transition.precondition(&system));
    }

    #[test]
    fn insert_slot_effect_adds_locus() {
        let system = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let result = transition.apply(&system).unwrap();
        assert!(result.contains_slot(new_slot));
        assert_eq!(result.slot_count(), system.slot_count() + 1);
    }

    #[test]
    fn insert_slot_effect_sets_type() {
        let system = make_test_system();
        let new_slot = SlotId(999);
        let new_slot_type = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Lax,
            lower: 2,
            upper: UpperBound::Finite(8),
            id: TypeId(42),
            meta: TypeMeta::None,
        };
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: new_slot_type.clone(),
        };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.type_of(new_slot), Some(&new_slot_type));
    }

    #[test]
    fn insert_slot_effect_does_not_change_relations() {
        let system = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.relations, system.relations);
    }

    #[test]
    fn delete_slot_precondition_fails_when_v_not_in_v() {
        let system = make_test_system();
        let transition = Transition::DeleteSlot { v: SlotId(999) };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn delete_slot_precondition_fails_when_only_one_slot() {
        let system = make_test_system();
        let (slot, _) = make_test_slot();
        let transition = Transition::DeleteSlot { v: slot };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn delete_slot_precondition_succeeds_when_valid() {
        let mut system = make_test_system();
        let (_, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type);
        let transition = Transition::DeleteSlot { v: slot2 };
        assert!(transition.precondition(&system));
    }

    #[test]
    fn delete_slot_effect_removes_slot() {
        let mut system = make_test_system();
        let (_, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type);
        let transition = Transition::DeleteSlot { v: slot2 };
        let result = transition.apply(&system).unwrap();
        assert!(!result.contains_slot(slot2));
        assert_eq!(result.slot_count(), system.slot_count() - 1);
    }

    #[test]
    fn delete_slot_effect_removes_relations_involving_v() {
        let mut system = make_test_system();
        let (slot1, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type);
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 0,
        });
        system.relations.push(Relation {
            source: slot2,
            target: slot1,
            position: 0,
        });
        let transition = Transition::DeleteSlot { v: slot2 };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.relations.len(), 0);
    }

    #[test]
    fn delete_slot_effect_does_not_affect_other_slots() {
        let mut system = make_test_system();
        let (slot1, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type);
        let transition = Transition::DeleteSlot { v: slot2 };
        let result = transition.apply(&system).unwrap();
        assert!(result.contains_slot(slot1));
        assert_eq!(result.type_of(slot1), system.type_of(slot1));
    }

    fn make_system_with_two_slots() -> (VCASystem, SlotId, SlotId) {
        let mut system = make_test_system();
        let (slot1, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type);
        (system, slot1, slot2)
    }

    fn make_system_with_rule() -> VCASystem {
        let rule_slot = SlotId(1);
        let data_slot = SlotId(2);

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };

        let mut system = VCASystem::new(rule_slot, rule_type).unwrap();
        system.slots.push(data_slot);
        system.types.insert(data_slot, data_type);
        system
    }

    #[test]
    fn attach_precondition_fails_when_u_not_in_v() {
        let system = make_test_system();
        let transition = Transition::Attach {
            u: SlotId(999),
            v: SlotId(1),
            i: 0,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn attach_precondition_fails_when_v_not_in_v() {
        let system = make_test_system();
        let (slot, _) = make_test_slot();
        let transition = Transition::Attach {
            u: slot,
            v: SlotId(999),
            i: 0,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn attach_precondition_fails_when_position_occupied() {
        let (mut system, slot1, slot2) = make_system_with_two_slots();
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 0,
        });
        let transition = Transition::Attach {
            u: SlotId(3),
            v: slot2,
            i: 0,
        };
        let mut test_system = system.clone();
        test_system.slots.push(SlotId(3));
        test_system.types.insert(
            SlotId(3),
            SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(1),
                meta: TypeMeta::None,
            },
        );
        assert!(!transition.precondition(&test_system));
    }

    #[test]
    fn attach_precondition_fails_when_not_admissible() {
        let mut system = make_system_with_rule();
        system.types.insert(
            system.slots[0],
            SlotType {
                family: Family::Rule,
                kind: Kind::None,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(1),
                meta: TypeMeta::None,
            },
        );
        let transition = Transition::Attach {
            u: system.slots[1],
            v: system.slots[1],
            i: 0,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn attach_precondition_fails_when_upper_bound_violated() {
        let (mut system, slot1, slot2) = make_system_with_two_slots();
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(1),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        system.types.insert(slot2, slot_type);
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 0,
        });
        let transition = Transition::Attach {
            u: SlotId(3),
            v: slot2,
            i: 1,
        };
        let mut test_system = system.clone();
        test_system.slots.push(SlotId(3));
        test_system.types.insert(
            SlotId(3),
            SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(1),
                meta: TypeMeta::None,
            },
        );
        assert!(!transition.precondition(&test_system));
    }

    #[test]
    fn attach_precondition_succeeds_when_all_conditions_met() {
        let system = make_system_with_rule();
        let transition = Transition::Attach {
            u: system.slots[1],
            v: system.slots[1],
            i: 0,
        };
        assert!(transition.precondition(&system));
    }

    #[test]
    fn attach_effect_adds_relation() {
        let system = make_system_with_rule();
        let transition = Transition::Attach {
            u: system.slots[1],
            v: system.slots[1],
            i: 0,
        };
        let result = transition.apply(&system).unwrap();
        assert!(result.relations.contains(&Relation {
            source: system.slots[1],
            target: system.slots[1],
            position: 0,
        }));
    }

    #[test]
    fn attach_effect_increases_src_count() {
        let system = make_system_with_rule();
        let initial_count = system.src_count(system.slots[1]);
        let transition = Transition::Attach {
            u: system.slots[1],
            v: system.slots[1],
            i: 0,
        };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.src_count(system.slots[1]), initial_count + 1);
    }

    #[test]
    fn attach_effect_does_not_change_slots_types() {
        let system = make_system_with_rule();
        let transition = Transition::Attach {
            u: system.slots[1],
            v: system.slots[1],
            i: 0,
        };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.slots, system.slots);
        assert_eq!(result.types, system.types);
    }

    #[test]
    fn detach_precondition_fails_when_relation_not_in_a() {
        let system = make_test_system();
        let transition = Transition::Detach {
            u: SlotId(1),
            v: SlotId(2),
            i: 0,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn detach_precondition_succeeds_when_relation_exists() {
        let (mut system, slot1, slot2) = make_system_with_two_slots();
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 0,
        });
        let transition = Transition::Detach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        assert!(transition.precondition(&system));
    }

    #[test]
    fn detach_effect_removes_relation() {
        let (mut system, slot1, slot2) = make_system_with_two_slots();
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 0,
        });
        let transition = Transition::Detach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let result = transition.apply(&system).unwrap();
        assert!(!result.relations.contains(&Relation {
            source: slot1,
            target: slot2,
            position: 0,
        }));
    }

    #[test]
    fn detach_effect_decreases_src_count() {
        let (mut system, slot1, slot2) = make_system_with_two_slots();
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 0,
        });
        let initial_count = system.src_count(slot2);
        let transition = Transition::Detach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.src_count(slot2), initial_count - 1);
    }

    #[test]
    fn detach_effect_does_not_change_slots_types() {
        let (mut system, slot1, slot2) = make_system_with_two_slots();
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 0,
        });
        let transition = Transition::Detach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.slots, system.slots);
        assert_eq!(result.types, system.types);
    }

    #[test]
    fn retype_precondition_fails_when_v_not_in_v() {
        let system = make_test_system();
        let (_, slot_type) = make_test_slot();
        let transition = Transition::Retype {
            v: SlotId(999),
            t: slot_type,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn retype_precondition_fails_when_type_not_well_formed() {
        let system = make_test_system();
        let (slot, _) = make_test_slot();
        let bad_slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 10,
            upper: UpperBound::Finite(5),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let transition = Transition::Retype {
            v: slot,
            t: bad_slot_type,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn retype_precondition_fails_when_src_count_exceeds_upper() {
        let (mut system, slot1, slot2) = make_system_with_two_slots();
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 0,
        });
        system.relations.push(Relation {
            source: slot1,
            target: slot2,
            position: 1,
        });
        let new_slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(1),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let transition = Transition::Retype {
            v: slot2,
            t: new_slot_type,
        };
        assert!(!transition.precondition(&system));
    }

    #[test]
    fn retype_precondition_succeeds_when_valid() {
        let system = make_test_system();
        let (slot, slot_type) = make_test_slot();
        let transition = Transition::Retype {
            v: slot,
            t: slot_type,
        };
        assert!(transition.precondition(&system));
    }

    #[test]
    fn retype_effect_updates_type() {
        let system = make_test_system();
        let (slot, _) = make_test_slot();
        let new_slot_type = SlotType {
            family: Family::Rule,
            kind: Kind::PatternMatch,
            layer: Layer::N(42),
            affinity: Affinity::Lax,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(99),
            meta: TypeMeta::None,
        };
        let transition = Transition::Retype {
            v: slot,
            t: new_slot_type.clone(),
        };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.type_of(slot), Some(&new_slot_type));
    }

    #[test]
    fn retype_effect_does_not_change_loci_or_relations() {
        let system = make_test_system();
        let (slot, slot_type) = make_test_slot();
        let transition = Transition::Retype {
            v: slot,
            t: slot_type,
        };
        let result = transition.apply(&system).unwrap();
        assert_eq!(result.slots, system.slots);
        assert_eq!(result.relations, system.relations);
    }

    #[test]
    fn apply_transition_calls_precondition_and_apply() {
        let system = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let result = apply_transition(&transition, &system).unwrap();
        assert!(result.contains_slot(new_slot));
    }

    #[test]
    fn apply_transition_returns_error_on_precondition_failure() {
        let system = make_test_system();
        let (slot, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: slot,
            t: slot_type,
        };
        let result = apply_transition(&transition, &system);
        assert!(result.is_err());
    }
}

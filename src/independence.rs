use std::collections::HashSet;

use crate::relation::PosIndex;
use crate::slot::SlotId;
use crate::system::VCASystem;
use crate::transitions::Transition;

/// A read/write location in the system: a slot, relation, or type assignment.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Location {
    Slot(SlotId),
    Relation(SlotId, SlotId, PosIndex),
    Type(SlotId),
}

/// Returns the set of locations read by a transition's precondition check.
pub fn read_set(transition: &Transition, system: &VCASystem) -> HashSet<Location> {
    let mut locations = HashSet::new();

    match transition {
        Transition::InsertSlot { .. } => {
            // reads nothing, checks v ∉ V
        }
        Transition::DeleteSlot { v } => {
            locations.insert(Location::Slot(*v));
        }
        Transition::Attach { u, v, i: _ } => {
            locations.insert(Location::Slot(*u));
            locations.insert(Location::Slot(*v));
            locations.insert(Location::Type(*u));
            locations.insert(Location::Type(*v));
            // check upper bound and position - need all relations targeting v for src_count and position check
            for rel in &system.relations {
                if rel.target == *v {
                    locations.insert(Location::Relation(rel.source, rel.target, rel.position));
                }
            }
        }
        Transition::Detach { u, v, i } => {
            locations.insert(Location::Relation(*u, *v, *i));
        }
        Transition::Retype { v, .. } => {
            locations.insert(Location::Slot(*v));
            locations.insert(Location::Type(*v));
            // check upper bound - need all relations targeting v for src_count
            for rel in &system.relations {
                if rel.target == *v {
                    locations.insert(Location::Relation(rel.source, rel.target, rel.position));
                }
            }
        }
    }

    locations
}

/// Returns the set of locations modified by a transition's effect.
pub fn write_set(transition: &Transition, system: &VCASystem) -> HashSet<Location> {
    let mut locations = HashSet::new();

    match transition {
        Transition::InsertSlot { v, .. } => {
            locations.insert(Location::Slot(*v));
            locations.insert(Location::Type(*v));
        }
        Transition::DeleteSlot { v } => {
            locations.insert(Location::Slot(*v));
            locations.insert(Location::Type(*v));
            // add all incident relations
            for rel in &system.relations {
                if rel.source == *v || rel.target == *v {
                    locations.insert(Location::Relation(rel.source, rel.target, rel.position));
                }
            }
        }
        Transition::Attach { u, v, i } => {
            locations.insert(Location::Relation(*u, *v, *i));
        }
        Transition::Detach { u, v, i } => {
            locations.insert(Location::Relation(*u, *v, *i));
        }
        Transition::Retype { v, .. } => {
            locations.insert(Location::Type(*v));
        }
    }

    locations
}

/// Returns true if two transitions commute: disjoint read/write sets (Theorem 11).
pub fn is_independent(t1: &Transition, t2: &Transition, system: &VCASystem) -> bool {
    if !t1.precondition(system) || !t2.precondition(system) {
        return false;
    }

    let w1 = write_set(t1, system);
    let r2 = read_set(t2, system);
    let w2 = write_set(t2, system);
    let r1 = read_set(t1, system);

    w1.is_disjoint(&r2) && w1.is_disjoint(&w2) && r1.is_disjoint(&w2)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::relation::Relation;
    use crate::system::RuleRef;
    use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};

    fn make_test_slot() -> (SlotId, crate::types::SlotType) {
        let slot = SlotId(1);
        let slot_type = crate::types::SlotType {
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

    fn normalize_system(mut system: VCASystem) -> VCASystem {
        // sort slots for consistent comparison (order doesn't matter semantically)
        system.slots.sort_by_key(|s| s.0);
        // sort relations for consistent comparison (order doesn't matter semantically)
        system
            .relations
            .sort_by_key(|r| (r.source.0, r.target.0, r.position));
        system
    }

    #[test]
    fn insert_slot_read_set_is_empty() {
        let system = make_test_system();
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: SlotId(999),
            t: slot_type,
        };
        let read = read_set(&transition, &system);
        assert!(read.is_empty());
    }

    #[test]
    fn insert_slot_write_set_contains_slot_and_type() {
        let system = make_test_system();
        let (_, slot_type) = make_test_slot();
        let v = SlotId(999);
        let transition = Transition::InsertSlot { v, t: slot_type };
        let write = write_set(&transition, &system);
        assert_eq!(write.len(), 2);
        assert!(write.contains(&Location::Slot(v)));
        assert!(write.contains(&Location::Type(v)));
    }

    #[test]
    fn delete_slot_read_set_contains_slot() {
        let mut system = make_test_system();
        let (_, slot_type) = make_test_slot();
        let v = SlotId(2);
        system.slots.push(v);
        system.types.insert(v, slot_type);
        let transition = Transition::DeleteSlot { v };
        let read = read_set(&transition, &system);
        assert_eq!(read.len(), 1);
        assert!(read.contains(&Location::Slot(v)));
    }

    #[test]
    fn delete_slot_write_set_includes_slot_type_and_incident_relations() {
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
            position: 1,
        });
        let transition = Transition::DeleteSlot { v: slot2 };
        let write = write_set(&transition, &system);
        assert!(write.contains(&Location::Slot(slot2)));
        assert!(write.contains(&Location::Type(slot2)));
        assert!(write.contains(&Location::Relation(slot1, slot2, 0)));
        assert!(write.contains(&Location::Relation(slot2, slot1, 1)));
        assert_eq!(write.len(), 4);
    }

    #[test]
    fn attach_read_set_contains_both_slots_and_types() {
        let mut system = make_test_system();
        let (slot1, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type);
        let transition = Transition::Attach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let read = read_set(&transition, &system);
        // read set includes: Slot(u), Slot(v), Type(u), Type(v), and relations targeting v (for src_count)
        assert!(read.len() >= 4);
        assert!(read.contains(&Location::Slot(slot1)));
        assert!(read.contains(&Location::Slot(slot2)));
        assert!(read.contains(&Location::Type(slot1)));
        assert!(read.contains(&Location::Type(slot2)));
    }

    #[test]
    fn attach_write_set_contains_relation() {
        let mut system = make_test_system();
        let (slot1, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type);
        let transition = Transition::Attach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let write = write_set(&transition, &system);
        assert_eq!(write.len(), 1);
        assert!(write.contains(&Location::Relation(slot1, slot2, 0)));
    }

    #[test]
    fn detach_read_set_contains_relation() {
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
        let transition = Transition::Detach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let read = read_set(&transition, &system);
        assert_eq!(read.len(), 1);
        assert!(read.contains(&Location::Relation(slot1, slot2, 0)));
    }

    #[test]
    fn detach_write_set_contains_relation() {
        let mut system = make_test_system();
        let (slot1, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type);
        let transition = Transition::Detach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let write = write_set(&transition, &system);
        assert_eq!(write.len(), 1);
        assert!(write.contains(&Location::Relation(slot1, slot2, 0)));
    }

    #[test]
    fn retype_read_set_contains_slot_and_type() {
        let system = make_test_system();
        let (slot, _) = make_test_slot();
        let (_, slot_type) = make_test_slot();
        let transition = Transition::Retype {
            v: slot,
            t: slot_type,
        };
        let read = read_set(&transition, &system);
        assert_eq!(read.len(), 2);
        assert!(read.contains(&Location::Slot(slot)));
        assert!(read.contains(&Location::Type(slot)));
    }

    #[test]
    fn retype_write_set_contains_type_only() {
        let system = make_test_system();
        let (slot, _) = make_test_slot();
        let (_, slot_type) = make_test_slot();
        let transition = Transition::Retype {
            v: slot,
            t: slot_type,
        };
        let write = write_set(&transition, &system);
        assert_eq!(write.len(), 1);
        assert!(write.contains(&Location::Type(slot)));
    }

    #[test]
    fn two_attach_to_different_slots_are_independent() {
        use crate::system::RuleRef;
        use crate::types::{Family, Kind, Layer, TypeId, TypeMeta, UpperBound};

        // create system with a rule slot so admissibility works
        let rule_slot = SlotId(1);
        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: crate::types::Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut system = VCASystem::new(rule_slot, rule_type).unwrap();

        let slot1 = SlotId(1);
        let slot2 = SlotId(2);
        let slot3 = SlotId(3);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: crate::types::Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        system.slots.push(slot2);
        system.slots.push(slot3);
        system.types.insert(slot2, data_type.clone());
        system.types.insert(slot3, data_type);
        system.rule_ref = RuleRef::SelfRef;

        let t1 = Transition::Attach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let t2 = Transition::Attach {
            u: slot1,
            v: slot3,
            i: 0,
        };

        assert!(is_independent(&t1, &t2, &system));
    }

    #[test]
    fn attach_and_detach_same_relation_are_not_independent() {
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

        let t1 = Transition::Attach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let t2 = Transition::Detach {
            u: slot1,
            v: slot2,
            i: 0,
        };

        assert!(!is_independent(&t1, &t2, &system));
    }

    #[test]
    fn two_insert_slot_with_different_ids_are_independent() {
        let system = make_test_system();
        let (_, slot_type) = make_test_slot();

        let t1 = Transition::InsertSlot {
            v: SlotId(100),
            t: slot_type.clone(),
        };
        let t2 = Transition::InsertSlot {
            v: SlotId(200),
            t: slot_type,
        };

        assert!(is_independent(&t1, &t2, &system));
    }

    #[test]
    fn insert_slot_and_delete_slot_same_id_are_not_independent() {
        let mut system = make_test_system();
        let (_, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type.clone());

        // insert and delete the same slot - should not be independent
        let t1 = Transition::InsertSlot {
            v: slot2,
            t: slot_type.clone(),
        };
        let t2 = Transition::DeleteSlot { v: slot2 };

        // t1 writes Slot(slot2), t2 reads Slot(slot2) - not independent
        // but t1's precondition fails (slot2 already exists), so is_independent returns false
        assert!(!is_independent(&t1, &t2, &system));
    }

    #[test]
    fn is_independent_returns_false_when_preconditions_fail() {
        let system = make_test_system();
        let (slot, slot_type) = make_test_slot();

        let t1 = Transition::InsertSlot {
            v: slot,
            t: slot_type.clone(),
        };
        let t2 = Transition::InsertSlot {
            v: SlotId(999),
            t: slot_type,
        };

        assert!(!is_independent(&t1, &t2, &system));
    }

    #[test]
    fn is_independent_checks_all_disjoint_conditions() {
        let mut system = make_test_system();
        let (slot1, slot_type) = make_test_slot();
        let slot2 = SlotId(2);
        system.slots.push(slot2);
        system.types.insert(slot2, slot_type.clone());

        let t1 = Transition::Retype {
            v: slot1,
            t: slot_type.clone(),
        };
        let t2 = Transition::Retype {
            v: slot2,
            t: slot_type,
        };

        assert!(is_independent(&t1, &t2, &system));
    }

    #[test]
    fn independent_transitions_commute() {
        // create system with a rule slot so admissibility works
        let rule_slot = SlotId(1);
        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: crate::types::Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut system = VCASystem::new(rule_slot, rule_type).unwrap();

        let slot1 = SlotId(1);
        let slot2 = SlotId(2);
        let slot3 = SlotId(3);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: crate::types::Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        system.slots.push(slot2);
        system.slots.push(slot3);
        system.types.insert(slot2, data_type.clone());
        system.types.insert(slot3, data_type);
        system.rule_ref = RuleRef::SelfRef;

        let t1 = Transition::Attach {
            u: slot1,
            v: slot2,
            i: 0,
        };
        let t2 = Transition::Attach {
            u: slot1,
            v: slot3,
            i: 0,
        };

        assert!(is_independent(&t1, &t2, &system));

        let system_t1_t2 = t1.apply(&system).unwrap();
        let system_t1_t2 = t2.apply(&system_t1_t2).unwrap();

        let system_t2_t1 = t2.apply(&system).unwrap();
        let system_t2_t1 = t1.apply(&system_t2_t1).unwrap();

        // normalize before comparing (slot order doesn't matter semantically)
        assert_eq!(
            normalize_system(system_t1_t2),
            normalize_system(system_t2_t1)
        );
    }

    #[test]
    fn independent_insert_slots_commute() {
        let system = make_test_system();
        let (_, slot_type) = make_test_slot();

        let t1 = Transition::InsertSlot {
            v: SlotId(100),
            t: slot_type.clone(),
        };
        let t2 = Transition::InsertSlot {
            v: SlotId(200),
            t: slot_type,
        };

        assert!(is_independent(&t1, &t2, &system));

        let system_t1_t2 = t1.apply(&system).unwrap();
        let system_t1_t2 = t2.apply(&system_t1_t2).unwrap();

        let system_t2_t1 = t2.apply(&system).unwrap();
        let system_t2_t1 = t1.apply(&system_t2_t1).unwrap();

        // normalize before comparing (slot order doesn't matter semantically)
        assert_eq!(
            normalize_system(system_t1_t2),
            normalize_system(system_t2_t1)
        );
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod proptest_tests {
    use super::*;
    use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};
    use proptest::prelude::*;

    fn normalize_system_for_proptest(mut system: VCASystem) -> VCASystem {
        // sort slots for consistent comparison (order doesn't matter semantically)
        system.slots.sort_by_key(|s| s.0);
        // sort relations for consistent comparison (order doesn't matter semantically)
        system
            .relations
            .sort_by_key(|r| (r.source.0, r.target.0, r.position));
        system
    }

    fn arbitrary_slot_type() -> impl Strategy<Value = SlotType> {
        (
            prop::sample::select(vec![Family::Data, Family::Rule]),
            prop::sample::select(vec![Kind::Any, Kind::None]),
            (0u32..10).prop_map(Layer::N),
            prop::sample::select(vec![Affinity::Strict, Affinity::Lax]),
            (0u32..5),
            prop::sample::select(vec![
                UpperBound::Finite(5),
                UpperBound::Finite(10),
                UpperBound::Infinite,
            ]),
            (1u64..1000).prop_map(TypeId),
        )
            .prop_map(
                |(family, kind, layer, affinity, lower, upper, id)| SlotType {
                    family,
                    kind,
                    layer,
                    affinity,
                    lower,
                    upper,
                    id,
                    meta: TypeMeta::None,
                },
            )
    }

    fn arbitrary_system() -> impl Strategy<Value = VCASystem> {
        arbitrary_slot_type().prop_map(|slot_type| {
            let slot = SlotId(1);
            VCASystem::new(slot, slot_type).expect("valid system")
        })
    }

    proptest! {
        #[test]
        fn independent_transitions_commute_theorem_11(
            system in arbitrary_system(),
            slot_id1 in (100u64..1000).prop_map(SlotId),
            slot_id2 in (2000u64..3000).prop_map(SlotId),
            slot_type1 in arbitrary_slot_type(),
            slot_type2 in arbitrary_slot_type(),
        ) {
            // ensure slots don't exist in system
            prop_assume!(!system.contains_slot(slot_id1));
            prop_assume!(!system.contains_slot(slot_id2));
            prop_assume!(slot_id1 != slot_id2);

            let t1 = Transition::InsertSlot {
                v: slot_id1,
                t: slot_type1,
            };
            let t2 = Transition::InsertSlot {
                v: slot_id2,
                t: slot_type2,
            };

            // only test if both are independent
            if is_independent(&t1, &t2, &system) {
                // apply t1 then t2
                let system_t1 = t1.apply(&system).expect("t1 should apply");
                let system_t1_t2 = t2.apply(&system_t1).expect("t2 should apply after t1");

                // apply t2 then t1
                let system_t2 = t2.apply(&system).expect("t2 should apply");
                let system_t2_t1 = t1.apply(&system_t2).expect("t1 should apply after t2");

                // normalize before comparing (slot order doesn't matter semantically)
                let normalized_t1_t2 = normalize_system_for_proptest(system_t1_t2);
                let normalized_t2_t1 = normalize_system_for_proptest(system_t2_t1);
                prop_assert_eq!(
                    normalized_t1_t2, normalized_t2_t1,
                    "independent transitions must commute (theorem 11)"
                );
            }
        }

        #[test]
        fn independent_retype_transitions_commute(
            system in arbitrary_system(),
            slot_id1 in (1u64..10).prop_map(SlotId),
            slot_id2 in (11u64..20).prop_map(SlotId),
            slot_type1 in arbitrary_slot_type(),
            slot_type2 in arbitrary_slot_type(),
        ) {
            // ensure both slots exist - create a modified system
            let mut modified_system = system.clone();
            if !modified_system.contains_slot(slot_id1) {
                modified_system.slots.push(slot_id1);
                modified_system.types.insert(slot_id1, slot_type1.clone());
            }
            if !modified_system.contains_slot(slot_id2) {
                modified_system.slots.push(slot_id2);
                modified_system.types.insert(slot_id2, slot_type2.clone());
            }
            prop_assume!(slot_id1 != slot_id2);

            let system = modified_system;

            // ensure types are well-formed and satisfy upper bounds
            let src_count1 = system.src_count(slot_id1);
            let src_count2 = system.src_count(slot_id2);
            let slot_type1_ok = slot_type1.upper_satisfied(src_count1);
            let slot_type2_ok = slot_type2.upper_satisfied(src_count2);
            prop_assume!(slot_type1_ok && slot_type2_ok);

            let t1 = Transition::Retype {
                v: slot_id1,
                t: slot_type1,
            };
            let t2 = Transition::Retype {
                v: slot_id2,
                t: slot_type2,
            };

            // only test if both are independent
            if is_independent(&t1, &t2, &system) {
                // apply t1 then t2
                let system_t1 = t1.apply(&system).expect("t1 should apply");
                let system_t1_t2 = t2.apply(&system_t1).expect("t2 should apply after t1");

                // apply t2 then t1
                let system_t2 = t2.apply(&system).expect("t2 should apply");
                let system_t2_t1 = t1.apply(&system_t2).expect("t1 should apply after t2");

                // normalize before comparing (slot order doesn't matter semantically)
                let normalized_t1_t2 = normalize_system_for_proptest(system_t1_t2);
                let normalized_t2_t1 = normalize_system_for_proptest(system_t2_t1);
                prop_assert_eq!(
                    normalized_t1_t2, normalized_t2_t1,
                    "independent retype transitions must commute (theorem 11)"
                );
            }
        }
    }
}

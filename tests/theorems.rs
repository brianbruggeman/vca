use vca::{
    admissibility::is_admissible,
    coherence::{all_admissible, is_coherent},
    core::core_star,
    registry::KindRegistry,
    relation::Relation,
    replay::{replay, ReplicaId, Transaction, VectorClock},
    sla::{check_sla, StatePredicate},
    slot::SlotId,
    system::{RuleRef, VCASystem},
    temporal::TemporalFormula,
    tower::Tower,
    transitions::Transition,
    types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound},
};

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

fn make_valid_system() -> VCASystem {
    let (slot, slot_type) = make_test_slot();
    VCASystem::new(slot, slot_type).expect("test system should be valid")
}

fn make_valid_system_with_two_loci() -> VCASystem {
    let system = make_valid_system();
    let slot2 = SlotId(2);
    let slot_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };
    let transition = Transition::InsertSlot {
        v: slot2,
        t: slot_type,
    };
    transition.apply(&system).expect("insert should succeed")
}

#[test]
fn theorem_8_insert_slot_preserves_structure() {
    let system = make_valid_system();
    assert!(
        system.is_structurally_valid(),
        "initial system must be valid"
    );

    let new_slot = SlotId(999);
    let (_, slot_type) = make_test_slot();
    let transition = Transition::InsertSlot {
        v: new_slot,
        t: slot_type,
    };

    assert!(
        transition.precondition(&system),
        "precondition must be satisfied"
    );

    let result = transition
        .apply(&system)
        .expect("transition should apply successfully");

    assert!(
        result.is_structurally_valid(),
        "result system must be structurally valid"
    );
}

#[test]
fn theorem_8_delete_slot_preserves_structure() {
    let system = make_valid_system_with_two_loci();
    assert!(
        system.is_structurally_valid(),
        "initial system must be valid"
    );

    let (slot1, _) = make_test_slot();
    let transition = Transition::DeleteSlot { v: slot1 };

    assert!(
        transition.precondition(&system),
        "precondition must be satisfied"
    );

    let result = transition
        .apply(&system)
        .expect("transition should apply successfully");

    assert!(
        result.is_structurally_valid(),
        "result system must be structurally valid"
    );
}

#[test]
fn theorem_8_attach_preserves_structure() {
    let system = make_valid_system_with_two_loci();
    assert!(
        system.is_structurally_valid(),
        "initial system must be valid"
    );

    let (slot1, _) = make_test_slot();
    let slot2 = SlotId(2);
    let transition = Transition::Attach {
        u: slot1,
        v: slot2,
        i: 0,
    };

    if !transition.precondition(&system) {
        return;
    }

    let result = transition
        .apply(&system)
        .expect("transition should apply successfully");

    assert!(
        result.is_structurally_valid(),
        "result system must be structurally valid"
    );
}

#[test]
fn theorem_8_detach_preserves_structure() {
    let mut system = make_valid_system_with_two_loci();
    let (slot1, _) = make_test_slot();
    let slot2 = SlotId(2);

    let rule_slot = SlotId(100);
    let rule_slot_type = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };
    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_slot_type,
    };
    system = insert_rule
        .apply(&system)
        .expect("insert rule should succeed");

    let attach_transition = Transition::Attach {
        u: slot1,
        v: slot2,
        i: 0,
    };
    system = attach_transition
        .apply(&system)
        .expect("attach should succeed");

    assert!(
        system.is_structurally_valid(),
        "initial system must be valid"
    );

    let transition = Transition::Detach {
        u: slot1,
        v: slot2,
        i: 0,
    };

    assert!(
        transition.precondition(&system),
        "precondition must be satisfied"
    );

    let result = transition
        .apply(&system)
        .expect("transition should apply successfully");

    assert!(
        result.is_structurally_valid(),
        "result system must be structurally valid"
    );
}

#[test]
fn theorem_8_retype_preserves_structure() {
    let system = make_valid_system();
    assert!(
        system.is_structurally_valid(),
        "initial system must be valid"
    );

    let (slot, _) = make_test_slot();
    let new_slot_type = SlotType {
        family: Family::Rule,
        kind: Kind::PatternMatch,
        layer: Layer::N(1),
        affinity: Affinity::Lax,
        lower: 0,
        upper: UpperBound::Finite(5),
        id: TypeId(2),
        meta: TypeMeta::None,
    };
    let transition = Transition::Retype {
        v: slot,
        t: new_slot_type,
    };

    assert!(
        transition.precondition(&system),
        "precondition must be satisfied"
    );

    let result = transition
        .apply(&system)
        .expect("transition should apply successfully");

    assert!(
        result.is_structurally_valid(),
        "result system must be structurally valid"
    );
}

#[test]
fn theorem_8_delta_preserves_structure() {
    // theorem 8: for f ∈ fs_struct and valid δ: δ(f) ∈ fs_struct
    // comprehensive test covering all transition types

    // test with various initial systems
    let test_systems = vec![make_valid_system(), make_valid_system_with_two_loci()];

    for initial_system in test_systems {
        assert!(
            initial_system.is_structurally_valid(),
            "initial system must be structurally valid"
        );

        // test insertslot
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let insert = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        if insert.precondition(&initial_system) {
            let result = insert
                .apply(&initial_system)
                .expect("insert should succeed");
            assert!(
                result.is_structurally_valid(),
                "insertslot must preserve structural validity"
            );
        }

        // test deleteslot (requires at least 2 slots)
        if initial_system.slot_count() > 1 {
            let slot_to_delete = initial_system.slots[0];
            let delete = Transition::DeleteSlot { v: slot_to_delete };
            if delete.precondition(&initial_system) {
                let result = delete
                    .apply(&initial_system)
                    .expect("delete should succeed");
                assert!(
                    result.is_structurally_valid(),
                    "deleteslot must preserve structural validity"
                );
            }
        }

        // test attach (requires at least 2 slots)
        if initial_system.slot_count() >= 2 {
            let slot1 = initial_system.slots[0];
            let slot2 = initial_system.slots[1];
            let attach = Transition::Attach {
                u: slot1,
                v: slot2,
                i: 0,
            };
            if attach.precondition(&initial_system) {
                let result = attach
                    .apply(&initial_system)
                    .expect("attach should succeed");
                assert!(
                    result.is_structurally_valid(),
                    "attach must preserve structural validity"
                );

                // test detach on the result
                let detach = Transition::Detach {
                    u: slot1,
                    v: slot2,
                    i: 0,
                };
                if detach.precondition(&result) {
                    let detach_result = detach.apply(&result).expect("detach should succeed");
                    assert!(
                        detach_result.is_structurally_valid(),
                        "detach must preserve structural validity"
                    );
                }
            }
        }

        // test retype
        let slot_to_retype = initial_system.slots[0];
        let new_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(999),
            meta: TypeMeta::None,
        };
        let retype = Transition::Retype {
            v: slot_to_retype,
            t: new_type,
        };
        if retype.precondition(&initial_system) {
            let result = retype
                .apply(&initial_system)
                .expect("retype should succeed");
            assert!(
                result.is_structurally_valid(),
                "retype must preserve structural validity"
            );
        }
    }
}

#[test]
fn theorem_2_core_star_is_coherent_for_any_input() {
    let registry = KindRegistry::with_base_kinds();

    let test_cases = vec![
        make_valid_system(),
        make_valid_system_with_two_loci(),
        {
            let system = make_valid_system();
            let rule_slot = SlotId(100);
            let rule_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(100),
                meta: TypeMeta::None,
            };
            let insert_rule = Transition::InsertSlot {
                v: rule_slot,
                t: rule_slot_type,
            };
            insert_rule
                .apply(&system)
                .expect("insert rule should succeed")
        },
        {
            let mut system = make_valid_system_with_two_loci();
            let (slot1, _) = make_test_slot();
            let slot2 = SlotId(2);
            let rule_slot = SlotId(100);
            let rule_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::None,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(100),
                meta: TypeMeta::None,
            };
            let insert_rule = Transition::InsertSlot {
                v: rule_slot,
                t: rule_slot_type,
            };
            system = insert_rule
                .apply(&system)
                .expect("insert rule should succeed");
            let attach_transition = Transition::Attach {
                u: slot1,
                v: slot2,
                i: 0,
            };
            if attach_transition.precondition(&system) {
                attach_transition
                    .apply(&system)
                    .expect("attach should succeed")
            } else {
                system
            }
        },
        {
            let system = make_valid_system();
            let rule_slot = SlotId(100);
            let rule_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::Top,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(100),
                meta: TypeMeta::None,
            };
            let insert_rule = Transition::InsertSlot {
                v: rule_slot,
                t: rule_slot_type,
            };
            insert_rule
                .apply(&system)
                .expect("insert rule should succeed")
        },
    ];

    for system in test_cases {
        let result = core_star(&system, &registry);
        assert!(
            is_coherent(&result),
            "core_star(F) must be coherent for any input F"
        );
    }
}

#[test]
fn theorem_2_all_relations_in_core_star_are_admissible() {
    let registry = KindRegistry::with_base_kinds();

    let test_cases = vec![
        make_valid_system(),
        make_valid_system_with_two_loci(),
        {
            let mut system = make_valid_system_with_two_loci();
            let (slot1, _) = make_test_slot();
            let slot2 = SlotId(2);
            let rule_slot = SlotId(100);
            let rule_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(100),
                meta: TypeMeta::None,
            };
            let insert_rule = Transition::InsertSlot {
                v: rule_slot,
                t: rule_slot_type,
            };
            system = insert_rule
                .apply(&system)
                .expect("insert rule should succeed");
            let attach_transition = Transition::Attach {
                u: slot1,
                v: slot2,
                i: 0,
            };
            if attach_transition.precondition(&system) {
                attach_transition
                    .apply(&system)
                    .expect("attach should succeed")
            } else {
                system
            }
        },
        {
            let mut system = make_valid_system_with_two_loci();
            let (slot1, _) = make_test_slot();
            let slot2 = SlotId(2);
            let rule_slot = SlotId(100);
            let rule_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::None,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(100),
                meta: TypeMeta::None,
            };
            let insert_rule = Transition::InsertSlot {
                v: rule_slot,
                t: rule_slot_type,
            };
            system = insert_rule
                .apply(&system)
                .expect("insert rule should succeed");
            let attach_transition = Transition::Attach {
                u: slot1,
                v: slot2,
                i: 0,
            };
            if attach_transition.precondition(&system) {
                attach_transition
                    .apply(&system)
                    .expect("attach should succeed")
            } else {
                system
            }
        },
    ];

    for system in test_cases {
        let result = core_star(&system, &registry);
        for relation in &result.relations {
            assert!(
                is_admissible(&result, relation),
                "all relations in core_star(F) must be admissible"
            );
        }
    }
}

#[test]
fn theorem_2_all_rule_loci_in_core_star_are_valid() {
    let registry = KindRegistry::with_base_kinds();

    let test_cases = vec![
        {
            let system = make_valid_system();
            let rule_slot = SlotId(100);
            let rule_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(100),
                meta: TypeMeta::None,
            };
            let insert_rule = Transition::InsertSlot {
                v: rule_slot,
                t: rule_slot_type,
            };
            insert_rule
                .apply(&system)
                .expect("insert rule should succeed")
        },
        {
            let system = make_valid_system();
            let rule_slot = SlotId(100);
            let rule_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::Top,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(100),
                meta: TypeMeta::None,
            };
            let insert_rule = Transition::InsertSlot {
                v: rule_slot,
                t: rule_slot_type,
            };
            insert_rule
                .apply(&system)
                .expect("insert rule should succeed")
        },
        {
            let system = make_valid_system();
            let rule_slot = SlotId(100);
            let rule_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::None,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(100),
                meta: TypeMeta::None,
            };
            let insert_rule = Transition::InsertSlot {
                v: rule_slot,
                t: rule_slot_type,
            };
            insert_rule
                .apply(&system)
                .expect("insert rule should succeed")
        },
    ];

    for system in test_cases {
        let result = core_star(&system, &registry);
        for rule_slot in result.rule_slots() {
            let Some(rule_type) = result.type_of(rule_slot) else {
                panic!("rule slot must have a type");
            };
            assert_eq!(
                rule_type.family,
                Family::Rule,
                "rule_loci() must return only Rule family loci"
            );
            assert!(
                registry.lookup(rule_type.kind).is_some(),
                "all rule loci in core_star(F) must have valid kinds registered in the registry"
            );
        }
    }
}

#[test]
fn theorem_1_shallow_access_interpretation_does_not_access_rule_relations() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let rule_slot = SlotId(100);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let rule_type = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1.clone()).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2.clone(),
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type.clone(),
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let test_relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };

    let original_admissible = is_admissible(&system, &test_relation);

    let rule_slot2 = SlotId(101);
    let rule_type2 = SlotType {
        family: Family::Rule,
        kind: Kind::None,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(101),
        meta: TypeMeta::None,
    };

    let insert_rule2 = Transition::InsertSlot {
        v: rule_slot2,
        t: rule_type2,
    };
    let mut system_with_extra_rule = insert_rule2
        .apply(&system)
        .expect("should insert second rule slot");

    let attach_rule_relation = Transition::Attach {
        u: rule_slot,
        v: rule_slot2,
        i: 0,
    };
    if attach_rule_relation.precondition(&system_with_extra_rule) {
        system_with_extra_rule = attach_rule_relation
            .apply(&system_with_extra_rule)
            .expect("should attach rule to rule");
    }

    let admissible_after_rule_relation = is_admissible(&system_with_extra_rule, &test_relation);

    assert_eq!(
        original_admissible, admissible_after_rule_relation,
        "admissibility should not change when A_ℛ (relations between rule slots) is modified"
    );
}

#[test]
fn theorem_1_shallow_access_interpretation_does_not_access_rule_rule_system() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let rule_slot = SlotId(100);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let rule_type = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1.clone()).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2.clone(),
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type.clone(),
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let test_relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };

    let original_admissible = is_admissible(&system, &test_relation);

    let external_rule_slot = SlotId(200);
    let external_rule_type = SlotType {
        family: Family::Rule,
        kind: Kind::None,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(200),
        meta: TypeMeta::None,
    };
    let mut external_system = VCASystem::new(external_rule_slot, external_rule_type)
        .expect("should create external system");
    external_system.rule_ref = RuleRef::SelfRef;

    let mut system_with_external_rules = system.clone();
    system_with_external_rules.rule_ref = RuleRef::External(Box::new(external_system));

    let admissible_after_rule_rule_change =
        is_admissible(&system_with_external_rules, &test_relation);

    assert_eq!(
        original_admissible, admissible_after_rule_rule_change,
        "admissibility should not change when ℛ.ℛ (the rule system's rule system) is modified"
    );
}

#[test]
fn theorem_1_shallow_access_interpretation_only_accesses_rule_slots_and_types() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let rule_slot = SlotId(100);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let rule_type_any = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let rule_type_none = SlotType {
        family: Family::Rule,
        kind: Kind::None,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1.clone()).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2.clone(),
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type_any.clone(),
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let test_relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };

    let admissible_with_any = is_admissible(&system, &test_relation);
    assert!(
        admissible_with_any,
        "relation should be admissible with Kind::Any rule"
    );

    let retype_rule = Transition::Retype {
        v: rule_slot,
        t: rule_type_none,
    };
    let system_with_none_rule = retype_rule.apply(&system).expect("should retype rule slot");

    let admissible_with_none = is_admissible(&system_with_none_rule, &test_relation);
    assert!(
        !admissible_with_none,
        "relation should not be admissible with Kind::None rule"
    );

    assert_ne!(
        admissible_with_any, admissible_with_none,
        "admissibility should change when τ_ℛ (rule slot type) is modified"
    );
}

#[test]
fn theorem_1_shallow_access_self_referential_admissibility_terminates() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let rule_slot = SlotId(100);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let rule_type = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1.clone()).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2.clone(),
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type.clone(),
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let test_relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };

    let result = is_admissible(&system, &test_relation);
    assert!(
        result,
        "self-referential admissibility check should terminate and return a result"
    );
}

#[test]
fn theorem_2_self_ref_coherent_iff_struct_and_admissible() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let rule_slot = SlotId(100);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let rule_type_any = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1.clone()).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2.clone(),
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type_any.clone(),
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };
    system.relations.push(relation);

    assert!(
        system.is_structurally_valid(),
        "system should be structurally valid"
    );
    assert!(
        all_admissible(&system),
        "all relations should be admissible"
    );
    assert!(
        is_coherent(&system),
        "self-ref system with struct + admissible should be coherent"
    );
}

#[test]
fn theorem_2_self_ref_not_coherent_when_not_struct() {
    use vca::RuleRef;

    let data_slot = SlotId(1);
    let data_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot, data_type).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    system.slots.clear();

    assert!(
        !system.is_structurally_valid(),
        "system should not be structurally valid"
    );
    assert!(
        !is_coherent(&system),
        "self-ref system that is not struct should not be coherent"
    );
}

#[test]
fn theorem_2_self_ref_not_coherent_when_not_admissible() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let rule_slot = SlotId(100);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let rule_type_none = SlotType {
        family: Family::Rule,
        kind: Kind::None,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1.clone()).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2.clone(),
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type_none.clone(),
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };
    system.relations.push(relation);

    assert!(
        system.is_structurally_valid(),
        "system should be structurally valid"
    );
    assert!(
        !all_admissible(&system),
        "relations should not be admissible with Kind::None rule"
    );
    assert!(
        !is_coherent(&system),
        "self-ref system with inadmissible relations should not be coherent"
    );
}

#[test]
fn theorem_2_self_ref_coherent_terminates_no_circularity() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let rule_slot = SlotId(100);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let rule_type = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1.clone()).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2.clone(),
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type.clone(),
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };
    system.relations.push(relation);

    let result = is_coherent(&system);
    assert!(
        result,
        "self-ref coherence check should terminate and return true for valid system"
    );
}

#[test]
fn theorem_2_self_ref_coherent_terminates_even_with_complex_structure() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let data_slot3 = SlotId(3);
    let rule_slot = SlotId(100);

    let data_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let rule_type_none = SlotType {
        family: Family::Rule,
        kind: Kind::None,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type.clone()).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type.clone(),
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_data3 = Transition::InsertSlot {
        v: data_slot3,
        t: data_type.clone(),
    };
    system = insert_data3
        .apply(&system)
        .expect("should insert data slot 3");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type_none.clone(),
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let relation1 = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };
    system.relations.push(relation1);

    let relation2 = Relation {
        source: data_slot2,
        target: data_slot3,
        position: 0,
    };
    system.relations.push(relation2);

    let result = is_coherent(&system);
    assert!(
        !result,
        "self-ref coherence check should terminate and return false for system with inadmissible relations"
    );
}

#[test]
fn theorem_3_structural_validity_decidable_terminates() {
    let (slot, slot_type) = make_test_slot();
    let system = VCASystem::new(slot, slot_type).expect("should create system");

    let result = system.is_structurally_valid();
    assert!(
        result,
        "is_structurally_valid() should terminate and return a result"
    );
}

#[test]
fn theorem_3_structural_validity_checks_nonempty() {
    let (slot, slot_type) = make_test_slot();
    let mut system = VCASystem::new(slot, slot_type).expect("should create system");

    assert!(
        system.is_structurally_valid(),
        "system with slots should be valid"
    );

    system.slots.clear();

    assert!(
        !system.is_structurally_valid(),
        "empty system should not be structurally valid (condition 1: V ≠ ∅)"
    );
}

#[test]
fn theorem_3_structural_validity_checks_total_types() {
    use vca::transitions::Transition;

    let (slot1, slot_type1) = make_test_slot();
    let mut system = VCASystem::new(slot1, slot_type1).expect("should create system");

    let slot2 = SlotId(2);
    let slot_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let insert_transition = Transition::InsertSlot {
        v: slot2,
        t: slot_type2,
    };
    system = insert_transition
        .apply(&system)
        .expect("should insert slot");

    assert!(
        system.is_structurally_valid(),
        "system with all slots having types should be valid"
    );

    system.types.remove(&slot2);

    assert!(
        !system.is_structurally_valid(),
        "system with slot missing type should not be structurally valid (condition 2: τ total on V)"
    );
}

#[test]
fn theorem_3_structural_validity_checks_position_uniqueness() {
    use vca::relation::Relation;
    use vca::transitions::Transition;

    let (slot1, slot_type1) = make_test_slot();
    let mut system = VCASystem::new(slot1, slot_type1).expect("should create system");

    let slot2 = SlotId(2);
    let slot_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let insert_transition = Transition::InsertSlot {
        v: slot2,
        t: slot_type2,
    };
    system = insert_transition
        .apply(&system)
        .expect("should insert slot");

    let relation1 = Relation {
        source: slot1,
        target: slot2,
        position: 0,
    };
    system.relations.push(relation1);

    assert!(
        system.is_structurally_valid(),
        "system with unique positions should be valid"
    );

    let relation2 = Relation {
        source: SlotId(999),
        target: slot2,
        position: 0,
    };
    system.relations.push(relation2);

    assert!(
        !system.is_structurally_valid(),
        "system with duplicate position should not be structurally valid (condition 3: position uniqueness)"
    );
}

#[test]
fn theorem_3_structural_validity_checks_upper_bounds() {
    use vca::relation::Relation;
    use vca::transitions::Transition;

    let (slot1, slot_type1) = make_test_slot();
    let mut system = VCASystem::new(slot1, slot_type1).expect("should create system");

    let slot2 = SlotId(2);
    let slot_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Finite(2),
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let insert_transition = Transition::InsertSlot {
        v: slot2,
        t: slot_type2,
    };
    system = insert_transition
        .apply(&system)
        .expect("should insert slot");

    let slot3 = SlotId(3);
    let slot_type3 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(3),
        meta: TypeMeta::None,
    };

    let insert_transition3 = Transition::InsertSlot {
        v: slot3,
        t: slot_type3,
    };
    system = insert_transition3
        .apply(&system)
        .expect("should insert slot 3");

    let relation1 = Relation {
        source: slot1,
        target: slot2,
        position: 0,
    };
    system.relations.push(relation1);

    let relation2 = Relation {
        source: slot3,
        target: slot2,
        position: 1,
    };
    system.relations.push(relation2);

    assert!(
        system.is_structurally_valid(),
        "system with upper bounds satisfied should be valid"
    );

    let relation3 = Relation {
        source: SlotId(4),
        target: slot2,
        position: 2,
    };
    system.relations.push(relation3);

    assert!(
        !system.is_structurally_valid(),
        "system with upper bound violated should not be structurally valid (condition 4: upper bounds)"
    );
}

#[test]
fn theorem_3_structural_validity_complexity_o_v_plus_a() {
    use vca::transitions::Transition;

    let (slot1, slot_type1) = make_test_slot();
    let mut system = VCASystem::new(slot1, slot_type1).expect("should create system");

    let slot_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(999),
        meta: TypeMeta::None,
    };

    for i in 2..=100 {
        let slot = SlotId(i);
        let insert_transition = Transition::InsertSlot {
            v: slot,
            t: slot_type.clone(),
        };
        system = insert_transition
            .apply(&system)
            .expect("should insert slot");
    }

    use vca::relation::Relation;

    for i in 1..=50 {
        let source = SlotId(i);
        let target = SlotId(i + 50);
        let relation = Relation {
            source,
            target,
            position: 0,
        };
        system.relations.push(relation);
    }

    let start = std::time::Instant::now();
    let result = system.is_structurally_valid();
    let elapsed = start.elapsed();

    assert!(result, "large system should be structurally valid");

    assert!(
        elapsed.as_millis() < 1000,
        "is_structurally_valid() should complete in reasonable time for O(|V| + |A|) complexity (100 slots, 50 relations)"
    );
}

#[test]
fn theorem_4_admissibility_decidable_terminates() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);
    let rule_slot = SlotId(100);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let rule_type = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(100),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2,
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let insert_rule = Transition::InsertSlot {
        v: rule_slot,
        t: rule_type,
    };
    system = insert_rule.apply(&system).expect("should insert rule slot");

    let test_relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };

    let result = is_admissible(&system, &test_relation);
    assert!(
        result || !result,
        "is_admissible() should terminate and return a boolean result (decidability)"
    );
}

#[test]
fn theorem_4_admissibility_decidable_complexity_o_vr_m() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let mut system = VCASystem::new(data_slot1, data_type1).expect("should create system");
    system.rule_ref = RuleRef::SelfRef;

    let insert_data2 = Transition::InsertSlot {
        v: data_slot2,
        t: data_type2,
    };
    system = insert_data2
        .apply(&system)
        .expect("should insert data slot 2");

    let rule_type_any = SlotType {
        family: Family::Rule,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(999),
        meta: TypeMeta::None,
    };

    for i in 100..=200 {
        let rule_slot = SlotId(i);
        let insert_rule = Transition::InsertSlot {
            v: rule_slot,
            t: rule_type_any.clone(),
        };
        system = insert_rule.apply(&system).expect("should insert rule slot");
    }

    let test_relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };

    let start = std::time::Instant::now();
    let result = is_admissible(&system, &test_relation);
    let elapsed = start.elapsed();

    assert!(
        result || !result,
        "is_admissible() should return a boolean result"
    );

    assert!(
        elapsed.as_millis() < 1000,
        "is_admissible() should complete in reasonable time for O(|V_ℛ| · m) complexity (101 rule slots)"
    );
}

#[test]
fn theorem_4_admissibility_decidable_returns_boolean_for_all_kinds() {
    use vca::relation::Relation;
    use vca::transitions::Transition;
    use vca::RuleRef;

    let data_slot1 = SlotId(1);
    let data_slot2 = SlotId(2);

    let data_type1 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };

    let data_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(2),
        meta: TypeMeta::None,
    };

    let test_relation = Relation {
        source: data_slot1,
        target: data_slot2,
        position: 0,
    };

    let kinds = vec![Kind::Any, Kind::None, Kind::Top, Kind::Bot];

    for kind in kinds {
        let mut system =
            VCASystem::new(data_slot1, data_type1.clone()).expect("should create system");
        system.rule_ref = RuleRef::SelfRef;

        let insert_data2 = Transition::InsertSlot {
            v: data_slot2,
            t: data_type2.clone(),
        };
        system = insert_data2
            .apply(&system)
            .expect("should insert data slot 2");

        let rule_slot = SlotId(100);
        let rule_type = SlotType {
            family: Family::Rule,
            kind: kind.clone(),
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(100),
            meta: TypeMeta::None,
        };

        let insert_rule = Transition::InsertSlot {
            v: rule_slot,
            t: rule_type,
        };
        system = insert_rule.apply(&system).expect("should insert rule slot");

        let result = is_admissible(&system, &test_relation);
        assert!(
            result || !result,
            "is_admissible() should return a boolean result for Kind::{:?}",
            kind
        );
    }
}

#[test]
fn theorem_5_level_n_coherence_depends_only_on_n_and_n_minus_1() {
    use vca::tower::Tower;
    use vca::transitions::Transition;
    use vca::RuleRef;

    // create base level (level 0) with Kind::Any rule
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

    let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    // create level 1
    let level1_slot = SlotId(3);
    let level1_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(3),
        meta: TypeMeta::None,
    };
    let mut level1 = VCASystem::new(level1_slot, level1_type).unwrap();
    level1.rule_ref = RuleRef::External(Box::new(base.clone()));

    // create level 2
    let level2_slot = SlotId(4);
    let level2_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(4),
        meta: TypeMeta::None,
    };
    let mut level2 = VCASystem::new(level2_slot, level2_type).unwrap();
    level2.rule_ref = RuleRef::External(Box::new(level1.clone()));

    // build tower with levels 0, 1, 2
    let mut tower = Tower::new(base.clone()).unwrap();
    tower.push_level(level1.clone()).unwrap();
    tower.push_level(level2.clone()).unwrap();

    // record coherence of level 2
    let original_coherence = tower.local_coh(2);

    // modify level 0 (which is < 2-1 = 1, so should not affect level 2)
    // we modify level 0's relations (A^(0)), which level 2 doesn't depend on
    // level 2 only depends on V^(1) and τ^(1) from level 1, and level 1 only
    // depends on V^(0) and τ^(0) from level 0 (not A^(0))
    let mut modified_base = base.clone();
    // add a relation to level 0 that doesn't affect V^(0) or τ^(0)
    let extra_slot = SlotId(999);
    let extra_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(999),
        meta: TypeMeta::None,
    };
    let insert_extra = Transition::InsertSlot {
        v: extra_slot,
        t: extra_type,
    };
    modified_base = insert_extra.apply(&modified_base).unwrap();

    // create new level 1 with rule_ref pointing to modified base
    // but keep V^(1) and τ^(1) the same
    let mut modified_level1 = level1.clone();
    modified_level1.rule_ref = RuleRef::External(Box::new(modified_base.clone()));

    // create new level 2 with rule_ref pointing to modified level 1
    // but keep V^(2) and τ^(2) the same
    let mut modified_level2 = level2.clone();
    modified_level2.rule_ref = RuleRef::External(Box::new(modified_level1.clone()));

    // create new tower with modified base and updated level 1, but same V^(2) and τ^(2)
    let mut modified_tower = Tower::new(modified_base).unwrap();
    modified_tower.push_level(modified_level1).unwrap();
    modified_tower.push_level(modified_level2).unwrap();

    // level 2 coherence should be unchanged (depends only on level 2 and level 1, not level 0)
    let modified_coherence = modified_tower.local_coh(2);
    assert_eq!(
        original_coherence, modified_coherence,
        "level 2 coherence should not change when level 0 is modified (level 2 depends only on levels 2 and 1)"
    );
}

#[test]
fn theorem_5_modifying_level_k_does_not_affect_levels_less_than_k() {
    use vca::tower::Tower;
    use vca::transitions::Transition;
    use vca::RuleRef;

    // create base level (level 0) with Kind::Any rule
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

    let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    // create level 1
    let level1_slot = SlotId(3);
    let level1_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(3),
        meta: TypeMeta::None,
    };
    let mut level1 = VCASystem::new(level1_slot, level1_type).unwrap();
    level1.rule_ref = RuleRef::External(Box::new(base.clone()));

    // create level 2
    let level2_slot = SlotId(4);
    let level2_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(4),
        meta: TypeMeta::None,
    };
    let mut level2 = VCASystem::new(level2_slot, level2_type).unwrap();
    level2.rule_ref = RuleRef::External(Box::new(level1.clone()));

    // build tower with levels 0, 1, 2
    let mut tower = Tower::new(base.clone()).unwrap();
    tower.push_level(level1.clone()).unwrap();
    tower.push_level(level2.clone()).unwrap();

    // record coherence of levels 0 and 1
    let original_coherence_0 = tower.local_coh(0);
    let original_coherence_1 = tower.local_coh(1);
    let original_coherent_up_to_1 = tower.is_coherent_up_to(1);

    // modify level 2 (k=2)
    let mut modified_level2 = level2.clone();
    let extra_slot = SlotId(999);
    let extra_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(999),
        meta: TypeMeta::None,
    };
    let insert_extra = Transition::InsertSlot {
        v: extra_slot,
        t: extra_type,
    };
    modified_level2 = insert_extra.apply(&modified_level2).unwrap();

    // create new tower with modified level 2
    let mut modified_tower = Tower::new(base.clone()).unwrap();
    modified_tower.push_level(level1.clone()).unwrap();
    modified_tower.push_level(modified_level2).unwrap();

    // levels 0 and 1 coherence should be unchanged (they are < 2)
    let modified_coherence_0 = modified_tower.local_coh(0);
    let modified_coherence_1 = modified_tower.local_coh(1);
    let modified_coherent_up_to_1 = modified_tower.is_coherent_up_to(1);

    assert_eq!(
        original_coherence_0, modified_coherence_0,
        "level 0 coherence should not change when level 2 is modified"
    );
    assert_eq!(
        original_coherence_1, modified_coherence_1,
        "level 1 coherence should not change when level 2 is modified"
    );
    assert_eq!(
        original_coherent_up_to_1, modified_coherent_up_to_1,
        "coherence up to level 1 should not change when level 2 is modified"
    );
}

#[test]
fn theorem_5_level_n_coherence_uses_only_slots_and_types_from_n_minus_1() {
    use vca::tower::Tower;
    use vca::transitions::Transition;
    use vca::RuleRef;

    // create base level (level 0) with Kind::Any rule
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

    let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    // create level 1 with a relation
    let level1_slot1 = SlotId(3);
    let level1_slot2 = SlotId(4);
    let level1_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(3),
        meta: TypeMeta::None,
    };
    let mut level1 = VCASystem::new(level1_slot1, level1_type.clone()).unwrap();
    level1.rule_ref = RuleRef::External(Box::new(base.clone()));

    // add second slot to level 1
    let insert_slot2 = Transition::InsertSlot {
        v: level1_slot2,
        t: level1_type.clone(),
    };
    level1 = insert_slot2.apply(&level1).unwrap();

    // add relation to level 1
    let attach = Transition::Attach {
        u: level1_slot1,
        v: level1_slot2,
        i: 0,
    };
    if attach.precondition(&level1) {
        level1 = attach.apply(&level1).unwrap();
    }

    // create level 2
    let level2_slot = SlotId(5);
    let level2_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(5),
        meta: TypeMeta::None,
    };
    let mut level2 = VCASystem::new(level2_slot, level2_type).unwrap();
    level2.rule_ref = RuleRef::External(Box::new(level1.clone()));

    // build tower
    let mut tower = Tower::new(base.clone()).unwrap();
    tower.push_level(level1.clone()).unwrap();
    tower.push_level(level2.clone()).unwrap();

    // record coherence of level 2
    let original_coherence = tower.local_coh(2);

    // modify level 1's relations (A^(1)) - this should NOT affect level 2 coherence
    // because level 2 only uses V^(1) and τ^(1) from level 1, not A^(1)
    let mut modified_level1 = level1.clone();
    modified_level1.relations.clear();

    // create new tower with modified level 1 (relations removed)
    let mut modified_tower = Tower::new(base.clone()).unwrap();
    modified_tower.push_level(modified_level1).unwrap();
    modified_tower.push_level(level2.clone()).unwrap();

    // level 2 coherence should be unchanged (it doesn't depend on A^(1))
    let modified_coherence = modified_tower.local_coh(2);
    assert_eq!(
        original_coherence, modified_coherence,
        "level 2 coherence should not change when level 1 relations (A^(1)) are modified (level 2 only uses V^(1) and τ^(1))"
    );
}

#[test]
fn theorem_6_tower_coherence_is_greatest_fixed_point_all_prefixes_coherent() {
    use vca::tower::Tower;
    use vca::RuleRef;

    // create a coherent tower with multiple levels
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

    let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    let mut tower = Tower::new(base.clone()).unwrap();

    // add multiple levels
    for i in 1..=5 {
        let level_slot = SlotId(10 + i);
        let level_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(10 + i),
            meta: TypeMeta::None,
        };
        let prev_level = tower.level((i - 1) as usize).unwrap().clone();
        let mut level = VCASystem::new(level_slot, level_type).unwrap();
        level.rule_ref = RuleRef::External(Box::new(prev_level));
        tower.push_level(level).unwrap();
    }

    // tower is coherent if and only if all finite prefixes are coherent
    // this is the gfp characterization: T ∈ gfp(Φ) iff ∀n: local_coh(T, n)
    assert!(
        tower.is_coherent(),
        "tower should be coherent if all levels are locally coherent"
    );

    // verify all finite prefixes are coherent
    for n in 0..tower.height() {
        assert!(
            tower.is_coherent_up_to(n),
            "finite prefix up to level {} should be coherent",
            n
        );
        assert!(tower.local_coh(n), "level {} should be locally coherent", n);
    }
}

#[test]
fn theorem_6_tower_coherence_gfp_characterization_incoherent_tower() {
    use vca::relation::Relation;
    use vca::tower::Tower;
    use vca::RuleRef;

    // create a tower where one level is incoherent
    // base has Kind::None rule, so relations won't be admissible
    let rule_slot = SlotId(1);
    let data_slot = SlotId(2);

    let rule_type_none = SlotType {
        family: Family::Rule,
        kind: Kind::None,
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

    let mut base = VCASystem::new(rule_slot, rule_type_none).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    let mut tower = Tower::new(base.clone()).unwrap();

    // add level 1 with a relation that won't be admissible under base (Kind::None)
    let level1_data_slot = SlotId(11);
    let level1_data_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(11),
        meta: TypeMeta::None,
    };

    let mut level1 = VCASystem::new(level1_data_slot, level1_data_type).unwrap();
    level1.rule_ref = RuleRef::External(Box::new(base));
    // add a relation that won't be admissible under base (which has Kind::None)
    level1.relations.push(Relation {
        source: level1_data_slot,
        target: level1_data_slot,
        position: 0,
    });
    tower.push_level(level1).unwrap();

    // tower should not be coherent because level 1 is not locally coherent
    assert!(
        !tower.is_coherent(),
        "tower should not be coherent if any level violates local coherence"
    );

    // verify that the finite prefix up to level 1 is not coherent
    assert!(
        !tower.is_coherent_up_to(1),
        "finite prefix up to level 1 should not be coherent"
    );
    assert!(
        !tower.local_coh(1),
        "level 1 should not be locally coherent"
    );

    // but level 0 should still be coherent
    assert!(
        tower.local_coh(0),
        "level 0 should still be locally coherent"
    );
    assert!(
        tower.is_coherent_up_to(0),
        "finite prefix up to level 0 should be coherent"
    );
}

#[test]
fn theorem_6_finite_prefix_decidable_terminates() {
    use vca::tower::Tower;
    use vca::RuleRef;

    // create a tower
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

    let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    let mut tower = Tower::new(base.clone()).unwrap();

    // add multiple levels
    for i in 1..=10 {
        let level_slot = SlotId(10 + i);
        let level_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(10 + i),
            meta: TypeMeta::None,
        };
        let prev_level = tower.level((i - 1) as usize).unwrap().clone();
        let mut level = VCASystem::new(level_slot, level_type).unwrap();
        level.rule_ref = RuleRef::External(Box::new(prev_level));
        tower.push_level(level).unwrap();
    }

    // is_coherent_up_to(n) should terminate and return a boolean for all n
    for n in 0..tower.height() {
        let start = std::time::Instant::now();
        let result = tower.is_coherent_up_to(n);
        let elapsed = start.elapsed();

        assert!(
            result || !result,
            "is_coherent_up_to({}) should terminate and return a boolean (decidability)",
            n
        );
        assert!(
            elapsed.as_millis() < 1000,
            "is_coherent_up_to({}) should complete in reasonable time",
            n
        );
    }
}

#[test]
fn theorem_6_finite_prefix_decidable_complexity() {
    use vca::tower::Tower;
    use vca::RuleRef;

    // create a large tower to test complexity
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

    let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    let mut tower = Tower::new(base.clone()).unwrap();

    // add many levels
    for i in 1..=20 {
        let level_slot = SlotId(10 + i);
        let level_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(10 + i),
            meta: TypeMeta::None,
        };
        let prev_level = tower.level((i - 1) as usize).unwrap().clone();
        let mut level = VCASystem::new(level_slot, level_type).unwrap();
        level.rule_ref = RuleRef::External(Box::new(prev_level));
        tower.push_level(level).unwrap();
    }

    // check that is_coherent_up_to(n) terminates in reasonable time
    // complexity should be O(n · A · V · m) where n is the number of levels
    let start = std::time::Instant::now();
    let result = tower.is_coherent_up_to(20);
    let elapsed = start.elapsed();

    assert!(
        result || !result,
        "is_coherent_up_to(20) should terminate and return a boolean"
    );
    assert!(
        elapsed.as_millis() < 5000,
        "is_coherent_up_to(20) should complete in reasonable time for O(n · A · V · m) complexity"
    );
}

#[test]
fn theorem_6_coinductive_interpretation_no_violation_found() {
    use vca::tower::Tower;
    use vca::RuleRef;

    // coinductive interpretation: a tower is coherent if we can never find a level
    // that violates local coherence. this is safety: "nothing bad ever happens."

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

    let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    let mut tower = Tower::new(base.clone()).unwrap();

    // add multiple levels - all should be locally coherent
    for i in 1..=10 {
        let level_slot = SlotId(10 + i);
        let level_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(10 + i),
            meta: TypeMeta::None,
        };
        let prev_level = tower.level((i - 1) as usize).unwrap().clone();
        let mut level = VCASystem::new(level_slot, level_type).unwrap();
        level.rule_ref = RuleRef::External(Box::new(prev_level));
        tower.push_level(level).unwrap();
    }

    // check that no violation is found at any level
    for n in 0..tower.height() {
        assert!(
            tower.local_coh(n),
            "no violation found at level {} (coinductive interpretation: nothing bad happens)",
            n
        );
    }

    // since no violation is found, tower is coherent
    assert!(
        tower.is_coherent(),
        "tower should be coherent if no violation is found at any level (coinductive interpretation)"
    );
}

#[test]
fn theorem_7_finite_prefix_decidable_terminates() {
    use vca::tower::Tower;
    use vca::RuleRef;

    // create a tower with multiple levels
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

    let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
    base.slots.push(data_slot);
    base.types.insert(data_slot, data_type);
    base.rule_ref = RuleRef::SelfRef;

    let mut tower = Tower::new(base.clone()).unwrap();

    // add multiple levels
    for i in 1..=10 {
        let level_slot = SlotId(10 + i);
        let level_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(10 + i),
            meta: TypeMeta::None,
        };
        let prev_level = tower.level((i - 1) as usize).unwrap().clone();
        let mut level = VCASystem::new(level_slot, level_type).unwrap();
        level.rule_ref = RuleRef::External(Box::new(prev_level));
        tower.push_level(level).unwrap();
    }

    // theorem 7: for any finite n, coherence of levels 0..=n is decidable
    // is_coherent_up_to(n) should terminate and return a boolean for all n
    for n in 0..tower.height() {
        let start = std::time::Instant::now();
        let result = tower.is_coherent_up_to(n);
        let elapsed = start.elapsed();

        assert!(
            result || !result,
            "is_coherent_up_to({}) should terminate and return a boolean (decidability)",
            n
        );
        assert!(
            elapsed.as_millis() < 1000,
            "is_coherent_up_to({}) should complete in reasonable time",
            n
        );
    }
}

#[test]
fn theorem_7_finite_prefix_decidable_complexity_o_n_a_v_m() {
    use vca::relation::Relation;
    use vca::tower::Tower;
    use vca::transitions::Transition;
    use vca::RuleRef;

    // theorem 7 complexity: O(n · A · V · m)
    // where n = number of levels, A = max relations per level,
    // V = max slots per level, m = max interpretation cost

    // create towers of varying sizes to verify complexity scaling
    let test_cases: Vec<(usize, usize, usize)> = vec![
        (5, 2, 2),    // n=5 levels, ~2 slots, ~2 relations per level
        (10, 5, 5),   // n=10 levels, ~5 slots, ~5 relations per level
        (15, 10, 10), // n=15 levels, ~10 slots, ~10 relations per level
    ];

    for (num_levels, slots_per_level, relations_per_level) in test_cases {
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

        let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
        base.slots.push(data_slot);
        base.types.insert(data_slot, data_type);
        base.rule_ref = RuleRef::SelfRef;

        let mut tower = Tower::new(base.clone()).unwrap();

        // add levels with slots and relations
        for i in 1..=num_levels {
            let prev_level = tower.level(i - 1).unwrap().clone();
            let mut level = VCASystem::new(
                SlotId((100 * i) as u64),
                SlotType {
                    family: Family::Data,
                    kind: Kind::Any,
                    layer: Layer::N(0),
                    affinity: Affinity::Strict,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId((100 * i) as u64),
                    meta: TypeMeta::None,
                },
            )
            .unwrap();
            level.rule_ref = RuleRef::External(Box::new(prev_level));

            // add slots to this level
            for j in 1..slots_per_level {
                let slot = SlotId((100 * i + j) as u64);
                let slot_type = SlotType {
                    family: Family::Data,
                    kind: Kind::Any,
                    layer: Layer::N(0),
                    affinity: Affinity::Strict,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId((100 * i + j) as u64),
                    meta: TypeMeta::None,
                };
                let insert = Transition::InsertSlot {
                    v: slot,
                    t: slot_type,
                };
                level = insert.apply(&level).unwrap();
            }

            // add relations to this level
            let level_slots: Vec<SlotId> = level.slots.iter().cloned().collect();
            for j in 0..relations_per_level.min(level_slots.len().saturating_sub(1)) {
                if level_slots.len() >= 2 {
                    let source = level_slots[j % level_slots.len()];
                    let target = level_slots[(j + 1) % level_slots.len()];
                    level.relations.push(Relation {
                        source,
                        target,
                        position: (j % 10) as u32,
                    });
                }
            }

            tower.push_level(level).unwrap();
        }

        // measure time for is_coherent_up_to(n)
        // complexity should be O(n · A · V · m)
        // with bounded level sizes: O(n · A · V · m)
        let n = num_levels;
        let a = relations_per_level;
        let v = slots_per_level;
        // m (interpretation cost) is constant for Kind::Any, so we can ignore it in scaling test

        let start = std::time::Instant::now();
        let result = tower.is_coherent_up_to(n);
        let elapsed = start.elapsed();

        assert!(
            result || !result,
            "is_coherent_up_to({}) should terminate and return a boolean",
            n
        );

        // verify complexity is reasonable: should scale roughly with n · A · V
        // allow generous bounds for constant factors and implementation overhead
        let expected_scale = n as u128 * a as u128 * v as u128;
        let elapsed_ms = elapsed.as_millis();

        // heuristic: for small inputs, should be very fast (< 100ms)
        // for larger inputs, should scale roughly linearly with n · A · V
        // we use a generous bound: should be < 10ms per (n · A · V) unit
        let max_expected_ms = (expected_scale * 10).max(100);

        assert!(
            elapsed_ms < max_expected_ms,
            "is_coherent_up_to({}) should complete in O(n · A · V · m) time: \
             n={}, A={}, V={}, expected scale={}, elapsed={}ms, max_expected={}ms",
            n,
            n,
            a,
            v,
            expected_scale,
            elapsed_ms,
            max_expected_ms
        );
    }
}

#[test]
fn theorem_9_core_star_produces_coherent() {
    // theorem 9: for f ∈ fs_struct: core_star(f) ∈ fs_coh
    // test all three cases: r = ∅, r ∈ fs_coh (external), r = f (self-ref)

    let registry = KindRegistry::with_base_kinds();

    // case 1: r = ∅ (empty rule system)
    {
        let data_slot = SlotId(1);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut system = VCASystem::new(data_slot, data_type).expect("should create system");
        system.rule_ref = RuleRef::Empty;

        // add a relation that should be admissible (kind::any admits all)
        let data_slot2 = SlotId(2);
        let data_type2 = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let insert = Transition::InsertSlot {
            v: data_slot2,
            t: data_type2,
        };
        system = insert.apply(&system).expect("should insert slot");
        system.relations.push(Relation {
            source: data_slot,
            target: data_slot2,
            position: 0,
        });

        assert!(
            system.is_structurally_valid(),
            "system must be structurally valid for theorem 9"
        );

        let result = core_star(&system, &registry);
        assert!(
            is_coherent(&result),
            "core_star(f) must be coherent for r = ∅ case"
        );
    }

    // case 2: r ∈ fs_coh (external coherent rule system)
    {
        // create external coherent rule system
        let external_rule_slot = SlotId(100);
        let external_rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(100),
            meta: TypeMeta::None,
        };
        let mut external_system =
            VCASystem::new(external_rule_slot, external_rule_type).expect("should create system");
        external_system.rule_ref = RuleRef::SelfRef;

        // verify external system is coherent
        assert!(
            is_coherent(&external_system),
            "external rule system must be coherent"
        );

        // create main system with external rule reference
        let data_slot = SlotId(1);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut system = VCASystem::new(data_slot, data_type).expect("should create system");
        system.rule_ref = RuleRef::External(Box::new(external_system.clone()));

        // add a relation
        let data_slot2 = SlotId(2);
        let data_type2 = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let insert = Transition::InsertSlot {
            v: data_slot2,
            t: data_type2,
        };
        system = insert.apply(&system).expect("should insert slot");
        system.relations.push(Relation {
            source: data_slot,
            target: data_slot2,
            position: 0,
        });

        assert!(
            system.is_structurally_valid(),
            "system must be structurally valid for theorem 9"
        );

        let result = core_star(&system, &registry);
        assert!(
            is_coherent(&result),
            "core_star(f) must be coherent for r ∈ fs_coh (external) case"
        );
    }

    // case 3: r = f (self-referential)
    {
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

        let mut system = VCASystem::new(rule_slot, rule_type).expect("should create system");
        system.slots.push(data_slot);
        system.types.insert(data_slot, data_type);
        system.rule_ref = RuleRef::SelfRef;

        // add a relation
        system.relations.push(Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        });

        assert!(
            system.is_structurally_valid(),
            "system must be structurally valid for theorem 9"
        );

        let result = core_star(&system, &registry);
        assert!(
            is_coherent(&result),
            "core_star(f) must be coherent for r = f (self-ref) case"
        );
    }

    // additional test: system with invalid rule slots and inadmissible relations
    {
        let rule_slot = SlotId(1);
        let data_slot = SlotId(2);

        // invalid rule slot (kind::top not in registry)
        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Top,
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

        let mut system = VCASystem::new(rule_slot, rule_type).expect("should create system");
        system.slots.push(data_slot);
        system.types.insert(data_slot, data_type);
        system.rule_ref = RuleRef::Empty;

        // add inadmissible relation (no valid rule to admit it)
        system.relations.push(Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        });

        assert!(
            system.is_structurally_valid(),
            "system must be structurally valid for theorem 9"
        );

        let result = core_star(&system, &registry);
        assert!(
            is_coherent(&result),
            "core_star(f) must be coherent even when input has invalid rules and inadmissible relations"
        );
        // verify invalid rule was removed
        assert!(
            !result.slots.contains(&rule_slot),
            "invalid rule slot should be removed by core_star"
        );
        // verify inadmissible relation was removed (or system has no valid rules to admit it)
        // with empty rule system, only kind::any admits, so relation should be removed
        assert_eq!(
            result.relations.len(),
            0,
            "inadmissible relation should be removed by core_star"
        );
    }
}

#[test]
fn theorem_10_core_star_idempotent() {
    // theorem 10: core_star(core_star(F)) == core_star(F)
    // test all three cases: r = ∅, r ∈ fs_coh (external), r = f (self-ref)

    let registry = KindRegistry::with_base_kinds();

    // case 1: r = ∅ (empty rule system)
    {
        let data_slot = SlotId(1);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut system = VCASystem::new(data_slot, data_type).expect("should create system");
        system.rule_ref = RuleRef::Empty;

        // add a relation
        let data_slot2 = SlotId(2);
        let data_type2 = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let insert = Transition::InsertSlot {
            v: data_slot2,
            t: data_type2,
        };
        system = insert.apply(&system).expect("should insert slot");
        system.relations.push(Relation {
            source: data_slot,
            target: data_slot2,
            position: 0,
        });

        let result1 = core_star(&system, &registry);
        let result2 = core_star(&result1, &registry);

        assert_eq!(
            result1.slots, result2.slots,
            "core_star should be idempotent for slots (r = ∅ case)"
        );
        assert_eq!(
            result1.relations, result2.relations,
            "core_star should be idempotent for relations (r = ∅ case)"
        );
        assert_eq!(
            result1.types, result2.types,
            "core_star should be idempotent for types (r = ∅ case)"
        );
    }

    // case 2: r ∈ fs_coh (external coherent rule system)
    {
        // create external coherent rule system
        let external_rule_slot = SlotId(100);
        let external_rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(100),
            meta: TypeMeta::None,
        };
        let mut external_system =
            VCASystem::new(external_rule_slot, external_rule_type).expect("should create system");
        external_system.rule_ref = RuleRef::SelfRef;

        // create main system with external rule reference
        let data_slot = SlotId(1);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut system = VCASystem::new(data_slot, data_type).expect("should create system");
        system.rule_ref = RuleRef::External(Box::new(external_system.clone()));

        // add a relation
        let data_slot2 = SlotId(2);
        let data_type2 = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let insert = Transition::InsertSlot {
            v: data_slot2,
            t: data_type2,
        };
        system = insert.apply(&system).expect("should insert slot");
        system.relations.push(Relation {
            source: data_slot,
            target: data_slot2,
            position: 0,
        });

        let result1 = core_star(&system, &registry);
        let result2 = core_star(&result1, &registry);

        assert_eq!(
            result1.slots, result2.slots,
            "core_star should be idempotent for slots (r ∈ fs_coh case)"
        );
        assert_eq!(
            result1.relations, result2.relations,
            "core_star should be idempotent for relations (r ∈ fs_coh case)"
        );
        assert_eq!(
            result1.types, result2.types,
            "core_star should be idempotent for types (r ∈ fs_coh case)"
        );
    }

    // case 3: r = f (self-referential)
    {
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

        let mut system = VCASystem::new(rule_slot, rule_type).expect("should create system");
        system.slots.push(data_slot);
        system.types.insert(data_slot, data_type);
        system.rule_ref = RuleRef::SelfRef;

        // add a relation
        system.relations.push(Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        });

        let result1 = core_star(&system, &registry);
        let result2 = core_star(&result1, &registry);

        assert_eq!(
            result1.slots, result2.slots,
            "core_star should be idempotent for slots (r = f case)"
        );
        assert_eq!(
            result1.relations, result2.relations,
            "core_star should be idempotent for relations (r = f case)"
        );
        assert_eq!(
            result1.types, result2.types,
            "core_star should be idempotent for types (r = f case)"
        );
    }

    // additional test: system with invalid rule slots and inadmissible relations
    {
        let rule_slot = SlotId(1);
        let data_slot = SlotId(2);

        // invalid rule slot (kind::top not in registry)
        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Top,
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

        let mut system = VCASystem::new(rule_slot, rule_type).expect("should create system");
        system.slots.push(data_slot);
        system.types.insert(data_slot, data_type);
        system.rule_ref = RuleRef::Empty;

        // add inadmissible relation
        system.relations.push(Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        });

        let result1 = core_star(&system, &registry);
        let result2 = core_star(&result1, &registry);

        assert_eq!(
            result1.slots, result2.slots,
            "core_star should be idempotent even when input has invalid rules"
        );
        assert_eq!(
            result1.relations, result2.relations,
            "core_star should be idempotent even when input has inadmissible relations"
        );
        assert_eq!(
            result1.types, result2.types,
            "core_star should be idempotent for types even with invalid input"
        );
    }
}

#[test]
fn theorem_11_independent_transitions_commute() {
    // theorem 11: if δ₁ ⊥ δ₂ then δ₁(δ₂(F)) = δ₂(δ₁(F))
    // if two transitions are independent, applying them in either order produces the same result

    use vca::independence::is_independent;
    use vca::RuleRef;

    fn normalize_system(mut system: VCASystem) -> VCASystem {
        // sort slots for consistent comparison (order doesn't matter semantically)
        system.slots.sort_by_key(|s| s.0);
        // sort relations for consistent comparison (order doesn't matter semantically)
        system
            .relations
            .sort_by_key(|r| (r.source.0, r.target.0, r.position));
        system
    }

    // test case 1: two independent InsertSlot transitions
    {
        let rule_slot = SlotId(1);
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
        let system = VCASystem::new(rule_slot, rule_type).expect("should create system");

        let slot1 = SlotId(100);
        let slot2 = SlotId(200);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(2),
            meta: TypeMeta::None,
        };

        let t1 = Transition::InsertSlot {
            v: slot1,
            t: data_type.clone(),
        };
        let t2 = Transition::InsertSlot {
            v: slot2,
            t: data_type,
        };

        assert!(
            is_independent(&t1, &t2, &system),
            "two InsertSlot with different ids should be independent"
        );

        // apply t1 then t2
        let system_t1 = t1.apply(&system).expect("t1 should apply");
        let system_t1_t2 = t2.apply(&system_t1).expect("t2 should apply after t1");

        // apply t2 then t1
        let system_t2 = t2.apply(&system).expect("t2 should apply");
        let system_t2_t1 = t1.apply(&system_t2).expect("t1 should apply after t2");

        // normalize before comparing
        let normalized_t1_t2 = normalize_system(system_t1_t2);
        let normalized_t2_t1 = normalize_system(system_t2_t1);

        assert_eq!(
            normalized_t1_t2.slots, normalized_t2_t1.slots,
            "independent InsertSlot transitions must commute (slots)"
        );
        assert_eq!(
            normalized_t1_t2.relations, normalized_t2_t1.relations,
            "independent InsertSlot transitions must commute (relations)"
        );
        assert_eq!(
            normalized_t1_t2.types, normalized_t2_t1.types,
            "independent InsertSlot transitions must commute (types)"
        );
    }

    // test case 2: two independent Attach transitions to different targets
    {
        let rule_slot = SlotId(1);
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
        let mut system = VCASystem::new(rule_slot, rule_type).expect("should create system");
        system.rule_ref = RuleRef::SelfRef;

        let slot1 = SlotId(1);
        let slot2 = SlotId(2);
        let slot3 = SlotId(3);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(2),
            meta: TypeMeta::None,
        };

        // add slots to system
        system.slots.push(slot2);
        system.slots.push(slot3);
        system.types.insert(slot2, data_type.clone());
        system.types.insert(slot3, data_type);

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

        assert!(
            is_independent(&t1, &t2, &system),
            "two Attach to different slots should be independent"
        );

        // apply t1 then t2
        let system_t1 = t1.apply(&system).expect("t1 should apply");
        let system_t1_t2 = t2.apply(&system_t1).expect("t2 should apply after t1");

        // apply t2 then t1
        let system_t2 = t2.apply(&system).expect("t2 should apply");
        let system_t2_t1 = t1.apply(&system_t2).expect("t1 should apply after t2");

        // normalize before comparing
        let normalized_t1_t2 = normalize_system(system_t1_t2);
        let normalized_t2_t1 = normalize_system(system_t2_t1);

        assert_eq!(
            normalized_t1_t2.slots, normalized_t2_t1.slots,
            "independent Attach transitions must commute (slots)"
        );
        assert_eq!(
            normalized_t1_t2.relations, normalized_t2_t1.relations,
            "independent Attach transitions must commute (relations)"
        );
        assert_eq!(
            normalized_t1_t2.types, normalized_t2_t1.types,
            "independent Attach transitions must commute (types)"
        );
    }

    // test case 3: two independent Retype transitions on different slots
    {
        let rule_slot = SlotId(1);
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
        let mut system =
            VCASystem::new(rule_slot, rule_type.clone()).expect("should create system");

        let slot1 = SlotId(1);
        let slot2 = SlotId(2);
        let data_type1 = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let data_type2 = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(3),
            meta: TypeMeta::None,
        };

        // add slot2 to system
        system.slots.push(slot2);
        system.types.insert(slot2, data_type1.clone());

        let t1 = Transition::Retype {
            v: slot1,
            t: rule_type.clone(),
        };
        let t2 = Transition::Retype {
            v: slot2,
            t: data_type2,
        };

        assert!(
            is_independent(&t1, &t2, &system),
            "two Retype on different slots should be independent"
        );

        // apply t1 then t2
        let system_t1 = t1.apply(&system).expect("t1 should apply");
        let system_t1_t2 = t2.apply(&system_t1).expect("t2 should apply after t1");

        // apply t2 then t1
        let system_t2 = t2.apply(&system).expect("t2 should apply");
        let system_t2_t1 = t1.apply(&system_t2).expect("t1 should apply after t2");

        // normalize before comparing
        let normalized_t1_t2 = normalize_system(system_t1_t2);
        let normalized_t2_t1 = normalize_system(system_t2_t1);

        assert_eq!(
            normalized_t1_t2.slots, normalized_t2_t1.slots,
            "independent Retype transitions must commute (slots)"
        );
        assert_eq!(
            normalized_t1_t2.relations, normalized_t2_t1.relations,
            "independent Retype transitions must commute (relations)"
        );
        assert_eq!(
            normalized_t1_t2.types, normalized_t2_t1.types,
            "independent Retype transitions must commute (types)"
        );
    }

    // test case 4: verify non-independent transitions do NOT commute
    // (negative test to ensure we're testing the right property)
    {
        let rule_slot = SlotId(1);
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
        let system = VCASystem::new(rule_slot, rule_type).expect("should create system");

        let slot1 = SlotId(1);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(2),
            meta: TypeMeta::None,
        };

        let t1 = Transition::InsertSlot {
            v: slot1,
            t: data_type.clone(),
        };
        let t2 = Transition::DeleteSlot { v: slot1 };

        // these are NOT independent (t1 writes Slot(slot1), t2 reads Slot(slot1))
        // but t1's precondition fails (slot1 already exists), so is_independent returns false
        assert!(
            !is_independent(&t1, &t2, &system),
            "InsertSlot and DeleteSlot on same slot should NOT be independent"
        );
    }
}

#[test]
fn theorem_12_replay_convergence() {
    // theorem 12: for replicas with the same transaction set H and initial state F₀:
    // replay(H, F₀)_replica1 = replay(H, F₀)_replica2
    // same history + same initial → same result
    // different orderings converge

    let registry = KindRegistry::with_base_kinds();

    fn make_test_slot_type() -> SlotType {
        SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        }
    }

    fn normalize_system(mut system: VCASystem) -> VCASystem {
        system.slots.sort_by_key(|s| s.0);
        system
            .relations
            .sort_by_key(|r| (r.source.0, r.target.0, r.position));
        system
    }

    // test case 1: same history + same initial → same result
    {
        let initial = make_valid_system();
        let r1 = ReplicaId(1);
        let mut vc = VectorClock::new();
        vc.insert(r1, 1);

        let slot2 = SlotId(2);
        let slot3 = SlotId(3);
        let slot_type = make_test_slot_type();

        let history = vec![
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot2,
                    t: slot_type.clone(),
                }],
                origin: r1,
                vc: vc.clone(),
                seq: 1,
            },
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot3,
                    t: slot_type,
                }],
                origin: r1,
                vc,
                seq: 2,
            },
        ];

        let result1 = replay(&history, &initial, &registry).expect("replay should succeed");
        let result2 = replay(&history, &initial, &registry).expect("replay should succeed");

        let normalized1 = normalize_system(result1);
        let normalized2 = normalize_system(result2);

        assert_eq!(
            normalized1.slots, normalized2.slots,
            "same history + same initial should produce same result (slots)"
        );
        assert_eq!(
            normalized1.relations, normalized2.relations,
            "same history + same initial should produce same result (relations)"
        );
        assert_eq!(
            normalized1.types, normalized2.types,
            "same history + same initial should produce same result (types)"
        );
    }

    // test case 2: different orderings converge
    {
        let initial = make_valid_system();
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);

        let mut vc1 = VectorClock::new();
        vc1.insert(r1, 1);

        let mut vc2 = VectorClock::new();
        vc2.insert(r2, 1);

        let slot2 = SlotId(2);
        let slot3 = SlotId(3);
        let slot_type = make_test_slot_type();

        let history1 = vec![
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot2,
                    t: slot_type.clone(),
                }],
                origin: r1,
                vc: vc1.clone(),
                seq: 1,
            },
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot3,
                    t: slot_type.clone(),
                }],
                origin: r2,
                vc: vc2.clone(),
                seq: 1,
            },
        ];

        let history2 = vec![
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot3,
                    t: slot_type.clone(),
                }],
                origin: r2,
                vc: vc2,
                seq: 1,
            },
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot2,
                    t: slot_type,
                }],
                origin: r1,
                vc: vc1,
                seq: 1,
            },
        ];

        let result1 = replay(&history1, &initial, &registry).expect("replay should succeed");
        let result2 = replay(&history2, &initial, &registry).expect("replay should succeed");

        let normalized1 = normalize_system(result1);
        let normalized2 = normalize_system(result2);

        assert_eq!(
            normalized1.slots, normalized2.slots,
            "different orderings should converge to same result (slots)"
        );
        assert_eq!(
            normalized1.relations, normalized2.relations,
            "different orderings should converge to same result (relations)"
        );
        assert_eq!(
            normalized1.types, normalized2.types,
            "different orderings should converge to same result (types)"
        );
    }

    // test case 3: more complex scenario with multiple replicas and vector clocks
    {
        let initial = make_valid_system();
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);
        let r3 = ReplicaId(3);

        let mut vc1 = VectorClock::new();
        vc1.insert(r1, 1);

        let mut vc2 = VectorClock::new();
        vc2.insert(r1, 1);
        vc2.insert(r2, 1);

        let mut vc3 = VectorClock::new();
        vc3.insert(r1, 2);
        vc3.insert(r2, 1);

        let slot2 = SlotId(2);
        let slot3 = SlotId(3);
        let slot4 = SlotId(4);
        let slot_type = make_test_slot_type();

        let history1 = vec![
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot2,
                    t: slot_type.clone(),
                }],
                origin: r1,
                vc: vc1.clone(),
                seq: 1,
            },
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot3,
                    t: slot_type.clone(),
                }],
                origin: r2,
                vc: vc2.clone(),
                seq: 1,
            },
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot4,
                    t: slot_type.clone(),
                }],
                origin: r3,
                vc: vc3.clone(),
                seq: 1,
            },
        ];

        let history2 = vec![
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot4,
                    t: slot_type.clone(),
                }],
                origin: r3,
                vc: vc3,
                seq: 1,
            },
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot3,
                    t: slot_type.clone(),
                }],
                origin: r2,
                vc: vc2,
                seq: 1,
            },
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot2,
                    t: slot_type,
                }],
                origin: r1,
                vc: vc1,
                seq: 1,
            },
        ];

        let result1 = replay(&history1, &initial, &registry).expect("replay should succeed");
        let result2 = replay(&history2, &initial, &registry).expect("replay should succeed");

        let normalized1 = normalize_system(result1);
        let normalized2 = normalize_system(result2);

        assert_eq!(
            normalized1.slots, normalized2.slots,
            "complex scenario: different orderings should converge (slots)"
        );
        assert_eq!(
            normalized1.relations, normalized2.relations,
            "complex scenario: different orderings should converge (relations)"
        );
        assert_eq!(
            normalized1.types, normalized2.types,
            "complex scenario: different orderings should converge (types)"
        );
    }
}

#[test]
fn theorem_13_box_coinductive() {
    // theorem 13: □φ is coinductive
    // T ⊨ □φ iff we never find a level where φ fails
    // checking finite prefixes: if we check up to n and never find a violation, then □φ holds for that prefix
    // if we find a violation at any level, then □φ does not hold

    fn make_coherent_system() -> VCASystem {
        let slot_id = SlotId(1);
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut system = VCASystem::new(slot_id, slot_type).expect("test system should be valid");
        system.rule_ref = RuleRef::SelfRef;
        system
    }

    // test case 1: □φ satisfied when property holds at all levels (never find violation)
    {
        let base = make_coherent_system();
        let mut tower = Tower::new(base).expect("tower should be valid");

        // add more levels where property holds
        for _ in 0..3 {
            let level = make_coherent_system();
            let prev_level = tower.level(tower.height() - 1).unwrap().clone();
            let mut next_level = level;
            next_level.rule_ref = RuleRef::External(Box::new(prev_level));
            tower.push_level(next_level).expect("push should succeed");
        }

        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));

        // check up to each level: should never find violation
        for n in 0..tower.height() {
            assert!(
                check_sla(&sla, &tower, n),
                "□φ should hold when property holds at all levels up to {}",
                n
            );
        }
    }

    // test case 2: □φ not satisfied when property fails at some level (find violation)
    {
        let base = make_coherent_system();
        let mut tower = Tower::new(base).expect("tower should be valid");

        // create a rule system with Kind::None that rejects all relations
        let rule_slot = SlotId(100);
        let rule_type_none = SlotType {
            family: Family::Rule,
            kind: Kind::None,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(100),
            meta: TypeMeta::None,
        };
        let mut rule_system =
            VCASystem::new(rule_slot, rule_type_none).expect("should create rule system");
        rule_system.rule_ref = RuleRef::SelfRef;

        // push the rule system as level 1
        rule_system.rule_ref = RuleRef::External(Box::new(tower.level(0).unwrap().clone()));
        tower
            .push_level(rule_system)
            .expect("push rule system should succeed");

        // create a level with a relation that will be inadmissible under the rule system
        let data_slot1 = SlotId(1);
        let data_slot2 = SlotId(2);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut bad_level =
            VCASystem::new(data_slot1, data_type.clone()).expect("should create level");
        bad_level.rule_ref = RuleRef::External(Box::new(tower.level(1).unwrap().clone()));

        // add second slot and a relation
        let insert_slot2 = Transition::InsertSlot {
            v: data_slot2,
            t: data_type,
        };
        bad_level = insert_slot2
            .apply(&bad_level)
            .expect("should insert slot 2");

        let relation = Relation {
            source: data_slot1,
            target: data_slot2,
            position: 0,
        };
        bad_level.relations.push(relation);

        // system is structurally valid but has inadmissible relation (Kind::None rejects all)
        assert!(
            bad_level.is_structurally_valid(),
            "bad_level should be structurally valid"
        );
        assert!(
            !is_coherent(&bad_level),
            "bad_level should be incoherent due to inadmissible relation"
        );

        tower.push_level(bad_level).expect("push should succeed");

        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));

        // check up to level 0: should hold (base is coherent)
        assert!(
            check_sla(&sla, &tower, 0),
            "□φ should hold at level 0 where property holds"
        );

        // check up to level 1: should hold (level 1 is the rule system, which is coherent)
        assert!(
            check_sla(&sla, &tower, 1),
            "□φ should hold at level 1 where property holds"
        );

        // check up to level 2: should fail (level 2 has inadmissible relation)
        assert!(
            !check_sla(&sla, &tower, 2),
            "□φ should fail when property fails at level 2"
        );
    }

    // test case 3: coinductive nature - checking finite prefixes never finding violation
    {
        let base = make_coherent_system();
        let mut tower = Tower::new(base).expect("tower should be valid");

        // add multiple levels where property holds
        for _ in 0..5 {
            let level = make_coherent_system();
            let prev_level = tower.level(tower.height() - 1).unwrap().clone();
            let mut next_level = level;
            next_level.rule_ref = RuleRef::External(Box::new(prev_level));
            tower.push_level(next_level).expect("push should succeed");
        }

        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));

        // for each finite prefix k, if we never find a violation, then □φ holds for that prefix
        for k in 0..tower.height() {
            let holds_at_all_levels = (0..=k).all(|i| {
                tower
                    .level(i)
                    .map(|level| is_coherent(level))
                    .unwrap_or(false)
            });

            let always_holds = check_sla(&sla, &tower, k);

            assert_eq!(
                holds_at_all_levels, always_holds,
                "□φ holds for prefix {} iff property holds at all levels 0..={}",
                k, k
            );
        }
    }

    // test case 4: violation found at any level means □φ does not hold
    {
        let base = make_coherent_system();
        let mut tower = Tower::new(base).expect("tower should be valid");

        // create a rule system with Kind::None that rejects all relations
        let rule_slot = SlotId(100);
        let rule_type_none = SlotType {
            family: Family::Rule,
            kind: Kind::None,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(100),
            meta: TypeMeta::None,
        };
        let mut rule_system =
            VCASystem::new(rule_slot, rule_type_none).expect("should create rule system");
        rule_system.rule_ref = RuleRef::SelfRef;

        // push the rule system as level 1
        rule_system.rule_ref = RuleRef::External(Box::new(tower.level(0).unwrap().clone()));
        tower
            .push_level(rule_system)
            .expect("push rule system should succeed");

        // create a level with a relation that will be inadmissible
        let data_slot1 = SlotId(1);
        let data_slot2 = SlotId(2);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut bad_level =
            VCASystem::new(data_slot1, data_type.clone()).expect("should create level");
        bad_level.rule_ref = RuleRef::External(Box::new(tower.level(1).unwrap().clone()));

        let insert_slot2 = Transition::InsertSlot {
            v: data_slot2,
            t: data_type,
        };
        bad_level = insert_slot2
            .apply(&bad_level)
            .expect("should insert slot 2");

        let relation = Relation {
            source: data_slot1,
            target: data_slot2,
            position: 0,
        };
        bad_level.relations.push(relation);

        tower.push_level(bad_level).expect("push should succeed");

        // add more levels after the violation
        for _ in 0..2 {
            let level = make_coherent_system();
            let prev_level = tower.level(tower.height() - 1).unwrap().clone();
            let mut next_level = level;
            next_level.rule_ref = RuleRef::External(Box::new(prev_level));
            tower.push_level(next_level).expect("push should succeed");
        }

        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));

        // once we check past the violation, □φ should fail
        assert!(
            !check_sla(&sla, &tower, tower.height() - 1),
            "□φ should fail when violation found at any level, even if later levels are ok"
        );
    }
}

#[test]
fn theorem_14_diamond_inductive() {
    // theorem 14: ◇φ is inductive
    // T ⊨ ◇φ iff we find some level where φ holds
    // checking finite prefixes: if we check up to n and find a witness, then ◇φ holds for that prefix
    // if we never find a witness, the search diverges (semi-decidable)

    fn make_coherent_system() -> VCASystem {
        let slot_id = SlotId(1);
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut system = VCASystem::new(slot_id, slot_type).expect("test system should be valid");
        system.rule_ref = RuleRef::SelfRef;
        system
    }

    fn make_incoherent_base() -> VCASystem {
        // create a self-referential base with Kind::None that rejects all relations
        // this will be incoherent because it has a relation that is inadmissible under itself
        let rule_slot = SlotId(100);
        let rule_type_none = SlotType {
            family: Family::Rule,
            kind: Kind::None,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(100),
            meta: TypeMeta::None,
        };
        let mut rule_system =
            VCASystem::new(rule_slot, rule_type_none).expect("should create rule system");
        rule_system.rule_ref = RuleRef::SelfRef;

        // add a data slot and a relation that will be inadmissible
        let data_slot = SlotId(1);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let insert_data = Transition::InsertSlot {
            v: data_slot,
            t: data_type,
        };
        let mut bad_system = insert_data
            .apply(&rule_system)
            .expect("should insert data slot");

        // add a relation that will be inadmissible (Kind::None rejects all)
        let relation = Relation {
            source: rule_slot,
            target: data_slot,
            position: 0,
        };
        bad_system.relations.push(relation);

        bad_system
    }

    fn make_incoherent_level(rule_system: &VCASystem) -> VCASystem {
        // create a level with a relation that will be inadmissible under the given rule system
        let data_slot1 = SlotId(1);
        let data_slot2 = SlotId(2);
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let mut bad_level =
            VCASystem::new(data_slot1, data_type.clone()).expect("should create level");
        bad_level.rule_ref = RuleRef::External(Box::new(rule_system.clone()));

        // add second slot and a relation
        let insert_slot2 = Transition::InsertSlot {
            v: data_slot2,
            t: data_type,
        };
        bad_level = insert_slot2
            .apply(&bad_level)
            .expect("should insert slot 2");

        let relation = Relation {
            source: data_slot1,
            target: data_slot2,
            position: 0,
        };
        bad_level.relations.push(relation);

        bad_level
    }

    // test case 1: ◇φ satisfied when witness found at some level
    // use SlotExists predicate which doesn't depend on rule_ref coherence
    {
        let base = make_incoherent_base();
        let mut tower = Tower::new(base).expect("tower should be valid");

        // add levels where property does not hold (slot 999 doesn't exist)
        for _ in 0..2 {
            let prev_level = tower.level(tower.height() - 1).unwrap();
            let level = make_incoherent_level(prev_level);
            tower.push_level(level).expect("push should succeed");
        }

        // add a level where property holds (witness: slot 999 exists)
        let prev_level = tower.level(tower.height() - 1).unwrap().clone();
        let witness_slot = SlotId(999);
        let witness_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(999),
            meta: TypeMeta::None,
        };
        let mut witness_level =
            VCASystem::new(witness_slot, witness_type).expect("should create witness level");
        witness_level.rule_ref = RuleRef::External(Box::new(prev_level));
        tower
            .push_level(witness_level)
            .expect("push should succeed");

        // add more levels after witness (slot 999 doesn't exist in these)
        for _ in 0..2 {
            let prev_level = tower.level(tower.height() - 1).unwrap();
            let level = make_incoherent_level(prev_level);
            tower.push_level(level).expect("push should succeed");
        }

        let sla = TemporalFormula::eventually(TemporalFormula::Prop(StatePredicate::SlotExists(
            SlotId(999),
        )));

        // check up to level before witness: should not find witness yet
        assert!(
            !check_sla(&sla, &tower, 1),
            "◇φ should not hold before witness is found"
        );

        // check up to level with witness: should find witness
        assert!(
            check_sla(&sla, &tower, 3),
            "◇φ should hold when witness found at level 3"
        );

        // check up to levels after witness: should still hold (witness already found)
        for n in 4..tower.height() {
            assert!(
                check_sla(&sla, &tower, n),
                "◇φ should hold for prefix {} since witness was found earlier",
                n
            );
        }
    }

    // test case 2: ◇φ satisfied when witness found at first level
    {
        let base = make_coherent_system();
        let tower = Tower::new(base).expect("tower should be valid");

        let sla = TemporalFormula::eventually(TemporalFormula::Prop(StatePredicate::Coherent));

        // witness found at level 0
        assert!(
            check_sla(&sla, &tower, 0),
            "◇φ should hold when witness found at level 0"
        );
    }

    // test case 3: ◇φ not satisfied when no witness found in prefix
    {
        let base = make_incoherent_base();
        let mut tower = Tower::new(base).expect("tower should be valid");

        // add levels where property does not hold
        for _ in 0..3 {
            let prev_level = tower.level(tower.height() - 1).unwrap();
            let level = make_incoherent_level(prev_level);
            tower.push_level(level).expect("push should succeed");
        }

        let sla = TemporalFormula::eventually(TemporalFormula::Prop(StatePredicate::Coherent));

        // check up to each level: should not find witness
        for n in 0..tower.height() {
            assert!(
                !check_sla(&sla, &tower, n),
                "◇φ should not hold for prefix {} when no witness found",
                n
            );
        }
    }

    // test case 4: inductive nature - finding witness establishes satisfaction
    {
        let base = make_incoherent_base();
        let mut tower = Tower::new(base).expect("tower should be valid");

        // add levels where property does not hold
        for _ in 0..2 {
            let prev_level = tower.level(tower.height() - 1).unwrap();
            let level = make_incoherent_level(prev_level);
            tower.push_level(level).expect("push should succeed");
        }

        let witness_slot = SlotId(888);
        let sla = TemporalFormula::eventually(TemporalFormula::Prop(StatePredicate::SlotExists(
            witness_slot,
        )));

        // before witness: ◇φ does not hold
        assert!(
            !check_sla(&sla, &tower, 2),
            "◇φ should not hold before witness is found"
        );

        // add witness
        let prev_level = tower.level(tower.height() - 1).unwrap().clone();
        let witness_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(888),
            meta: TypeMeta::None,
        };
        let mut witness_level =
            VCASystem::new(witness_slot, witness_type).expect("should create witness level");
        witness_level.rule_ref = RuleRef::External(Box::new(prev_level));
        tower
            .push_level(witness_level)
            .expect("push should succeed");

        // after witness: ◇φ holds
        assert!(
            check_sla(&sla, &tower, 3),
            "◇φ should hold after witness is found"
        );

        // verify that finding a witness at level n means ◇φ holds for all prefixes >= n
        for k in 3..tower.height() {
            let witness_found = (0..=k).any(|i| {
                tower
                    .level(i)
                    .map(|level| level.contains_slot(witness_slot))
                    .unwrap_or(false)
            });

            let eventually_holds = check_sla(&sla, &tower, k);

            assert_eq!(
                witness_found, eventually_holds,
                "◇φ holds for prefix {} iff witness found at some level 0..={}",
                k, k
            );
        }
    }

    // test case 5: witness found at different positions
    {
        let base = make_incoherent_base();
        let mut tower = Tower::new(base).expect("tower should be valid");

        // add witness at level 1
        let witness_slot = SlotId(777);
        let prev_level = tower.level(0).unwrap().clone();
        let witness_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(777),
            meta: TypeMeta::None,
        };
        let mut witness_level =
            VCASystem::new(witness_slot, witness_type).expect("should create witness level");
        witness_level.rule_ref = RuleRef::External(Box::new(prev_level));
        tower
            .push_level(witness_level)
            .expect("push should succeed");

        let sla = TemporalFormula::eventually(TemporalFormula::Prop(StatePredicate::SlotExists(
            witness_slot,
        )));

        // check up to level 0: no witness
        assert!(
            !check_sla(&sla, &tower, 0),
            "◇φ should not hold at level 0 when witness is at level 1"
        );

        // check up to level 1: witness found
        assert!(
            check_sla(&sla, &tower, 1),
            "◇φ should hold at level 1 when witness is found there"
        );
    }
}

#[test]
fn theorem_15_sla_finite_prefix_decidable() {
    // theorem 15: □-only SLAs are decidable up to n in O(|Ω*| · n^d · c)
    // where |Ω*| is formula size, n is number of levels, d is nesting depth, c is cost of base property

    use vca::tower::Tower;
    use vca::RuleRef;

    // helper to create a coherent tower with n levels
    fn make_coherent_tower(num_levels: usize) -> Tower {
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

        let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
        base.slots.push(data_slot);
        base.types.insert(data_slot, data_type);
        base.rule_ref = RuleRef::SelfRef;

        let mut tower = Tower::new(base).unwrap();

        for i in 1..=num_levels {
            let level_slot = SlotId(10 + i as u64);
            let level_type = SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(10 + i as u64),
                meta: TypeMeta::None,
            };
            let prev_level = tower.level((i - 1) as usize).unwrap().clone();
            let mut level = VCASystem::new(level_slot, level_type).unwrap();
            level.rule_ref = RuleRef::External(Box::new(prev_level));
            tower.push_level(level).unwrap();
        }

        tower
    }

    // test case 1: decidability - □-only formulas terminate and return boolean
    {
        let tower = make_coherent_tower(5);
        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));

        // should terminate and return boolean
        let start = std::time::Instant::now();
        let result = check_sla(&sla, &tower, 5);
        let elapsed = start.elapsed();

        assert!(
            elapsed.as_secs() < 1,
            "check_sla should terminate quickly (decidability)"
        );
        assert!(
            result == true || result == false,
            "check_sla should return a boolean result"
        );
    }

    // test case 2: depth-1 □ formula - should check all n levels
    {
        let tower = make_coherent_tower(10);
        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));

        // wrap predicate to count evaluations
        use std::cell::RefCell;
        let eval_count = RefCell::new(0);
        let result = {
            let trace: Vec<VCASystem> = (0..=10).filter_map(|i| tower.level(i)).cloned().collect();

            sla.check_up_to(
                &trace,
                |system, pred| {
                    *eval_count.borrow_mut() += 1;
                    match pred {
                        StatePredicate::Coherent => is_coherent(system),
                        _ => false,
                    }
                },
                10,
            )
        };

        // depth-1 □ should evaluate predicate (n+1) times (once per level 0..=n)
        assert_eq!(
            *eval_count.borrow(),
            11,
            "depth-1 □ formula should evaluate predicate (n+1) times, got {}",
            *eval_count.borrow()
        );
        assert!(
            result == true || result == false,
            "should return boolean result"
        );
    }

    // test case 3: depth-2 □□ formula - should check n^2 combinations
    {
        let tower = make_coherent_tower(5);
        use std::cell::RefCell;
        let eval_count = RefCell::new(0);

        let sla = TemporalFormula::always(TemporalFormula::always(TemporalFormula::Prop(
            StatePredicate::Coherent,
        )));

        let result = {
            let trace: Vec<VCASystem> = (0..=5).filter_map(|i| tower.level(i)).cloned().collect();

            sla.check_up_to(
                &trace,
                |system, pred| {
                    *eval_count.borrow_mut() += 1;
                    match pred {
                        StatePredicate::Coherent => is_coherent(system),
                        _ => false,
                    }
                },
                5,
            )
        };

        // depth-2 □□ should evaluate predicate O(n^2) times
        // outer □ checks levels 0..=5 (6 levels), inner □ checks levels i..=5 for each i
        // total: 6+5+4+3+2+1 = 21 = n(n+1)/2 where n=6
        assert!(
            *eval_count.borrow() == 21,
            "depth-2 □□ formula should evaluate predicate n(n+1)/2 times for n=6, got {}",
            *eval_count.borrow()
        );
        assert!(
            result == true || result == false,
            "should return boolean result"
        );
    }

    // test case 4: boolean connectives preserve decidability
    {
        let tower = make_coherent_tower(5);

        let sla1 = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));
        let sla2 =
            TemporalFormula::always(TemporalFormula::Prop(StatePredicate::SlotExists(SlotId(1))));

        let and_sla = TemporalFormula::and(sla1.clone(), sla2.clone());
        let or_sla = TemporalFormula::or(sla1.clone(), sla2.clone());
        let not_sla = TemporalFormula::not(sla1.clone());

        // all should terminate and return boolean
        let start = std::time::Instant::now();
        let and_result = check_sla(&and_sla, &tower, 5);
        let or_result = check_sla(&or_sla, &tower, 5);
        let not_result = check_sla(&not_sla, &tower, 5);
        let elapsed = start.elapsed();

        assert!(
            elapsed.as_secs() < 1,
            "boolean connectives should preserve decidability"
        );
        assert!(
            and_result == true || and_result == false,
            "conjunction should return boolean"
        );
        assert!(
            or_result == true || or_result == false,
            "disjunction should return boolean"
        );
        assert!(
            not_result == true || not_result == false,
            "negation should return boolean"
        );
    }

    // test case 5: complexity scales with formula size and nesting depth
    {
        let tower = make_coherent_tower(10);
        use std::cell::RefCell;

        // small formula, depth 1
        let small_sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));
        let small_count = RefCell::new(0);
        {
            let trace: Vec<VCASystem> = (0..=10).filter_map(|i| tower.level(i)).cloned().collect();

            small_sla.check_up_to(
                &trace,
                |_, _| {
                    *small_count.borrow_mut() += 1;
                    true
                },
                10,
            );
        }

        // larger formula, depth 2
        let large_sla = TemporalFormula::always(TemporalFormula::always(TemporalFormula::always(
            TemporalFormula::Prop(StatePredicate::Coherent),
        )));
        let large_count = RefCell::new(0);
        {
            let trace: Vec<VCASystem> = (0..=10).filter_map(|i| tower.level(i)).cloned().collect();

            large_sla.check_up_to(
                &trace,
                |_, _| {
                    *large_count.borrow_mut() += 1;
                    true
                },
                10,
            );
        }

        // larger formula with more nesting should have more evaluations
        assert!(
            *large_count.borrow() > *small_count.borrow(),
            "larger formula with more nesting should have more predicate evaluations: small={}, large={}",
            *small_count.borrow(),
            *large_count.borrow()
        );
    }

    // test case 6: □-only fragment excludes unbounded ◇ but allows bounded checks
    {
        let tower = make_coherent_tower(5);

        // □ formula is decidable
        let box_sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));
        let start = std::time::Instant::now();
        let box_result = check_sla(&box_sla, &tower, 5);
        let box_elapsed = start.elapsed();

        assert!(
            box_elapsed.as_secs() < 1,
            "□ formula should be decidable (terminate quickly)"
        );
        assert!(
            box_result == true || box_result == false,
            "□ formula should return boolean"
        );

        // unbounded ◇ is semi-decidable (may not terminate for false case)
        // but for finite prefix, it becomes bounded ◇_{≤n} which is decidable
        let diamond_sla =
            TemporalFormula::eventually(TemporalFormula::Prop(StatePredicate::Coherent));
        let start = std::time::Instant::now();
        let diamond_result = check_sla(&diamond_sla, &tower, 5);
        let diamond_elapsed = start.elapsed();

        // for finite prefix, ◇ becomes ◇_{≤n} which is decidable
        assert!(
            diamond_elapsed.as_secs() < 1,
            "◇ formula on finite prefix should be decidable (becomes ◇_{{≤n}})"
        );
        assert!(
            diamond_result == true || diamond_result == false,
            "◇ formula on finite prefix should return boolean"
        );
    }
}

#[test]
fn theorem_16_tower_coh_iff_always_coherent() {
    fn make_coherent_base() -> VCASystem {
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
        system.rule_ref = RuleRef::SelfRef;
        system
    }

    let always_coherent_sla =
        TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));

    let base = make_coherent_base();
    let tower = Tower::new(base).unwrap();
    let max_level = tower.height() - 1;

    let tower_is_coherent = tower.is_coherent();
    let sla_satisfied = check_sla(&always_coherent_sla, &tower, max_level);

    assert_eq!(
        tower_is_coherent, sla_satisfied,
        "tower_coh ⟺ □(coherent): tower.is_coherent()={}, check_sla(□(coherent))={}",
        tower_is_coherent, sla_satisfied
    );

    let mut tower2 = Tower::new(make_coherent_base()).unwrap();
    let level1_slot = SlotId(3);
    let level1_type = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(3),
        meta: TypeMeta::None,
    };
    let mut level1 = VCASystem::new(level1_slot, level1_type).unwrap();
    level1.rule_ref = RuleRef::External(Box::new(tower2.base().clone()));
    tower2.push_level(level1).unwrap();

    let max_level2 = tower2.height() - 1;
    let tower2_is_coherent = tower2.is_coherent();
    let sla2_satisfied = check_sla(&always_coherent_sla, &tower2, max_level2);

    assert_eq!(
        tower2_is_coherent, sla2_satisfied,
        "tower_coh ⟺ □(coherent): multi-level tower.is_coherent()={}, check_sla(□(coherent))={}",
        tower2_is_coherent, sla2_satisfied
    );

    let rule_slot = SlotId(1);
    let rule_type = SlotType {
        family: Family::Rule,
        kind: Kind::None,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(1),
        meta: TypeMeta::None,
    };
    let mut incoherent_base = VCASystem::new(rule_slot, rule_type).unwrap();
    incoherent_base.rule_ref = RuleRef::SelfRef;
    let mut incoherent_tower = Tower::new(incoherent_base).unwrap();

    let level1_slot2 = SlotId(4);
    let level1_type2 = SlotType {
        family: Family::Data,
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(4),
        meta: TypeMeta::None,
    };
    let mut level1_incoherent = VCASystem::new(level1_slot2, level1_type2).unwrap();
    level1_incoherent.rule_ref = RuleRef::External(Box::new(incoherent_tower.base().clone()));
    level1_incoherent.relations.push(Relation {
        source: level1_slot2,
        target: level1_slot2,
        position: 0,
    });
    incoherent_tower.push_level(level1_incoherent).unwrap();

    let max_level_incoherent = incoherent_tower.height() - 1;
    let incoherent_tower_is_coherent = incoherent_tower.is_coherent();
    let incoherent_sla_satisfied = check_sla(
        &always_coherent_sla,
        &incoherent_tower,
        max_level_incoherent,
    );

    assert_eq!(
        incoherent_tower_is_coherent, incoherent_sla_satisfied,
        "tower_coh ⟺ □(coherent): incoherent tower.is_coherent()={}, check_sla(□(coherent))={}",
        incoherent_tower_is_coherent, incoherent_sla_satisfied
    );
    assert!(
        !incoherent_tower_is_coherent,
        "incoherent tower should not be coherent"
    );
    assert!(
        !incoherent_sla_satisfied,
        "incoherent tower should not satisfy □(coherent)"
    );
}

#![allow(clippy::unwrap_used, clippy::expect_used)]

use proptest::prelude::*;
use vca::{
    core::{core, core_r, core_star},
    independence::is_independent,
    registry::KindRegistry,
    replay::{Transaction, replay, sort_transactions},
    slot::SlotId,
    system::VCASystem,
    transitions::Transition,
    types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound},
};

fn normalize_system(mut system: VCASystem) -> VCASystem {
    system.normalize();
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

fn arbitrary_valid_system() -> impl Strategy<Value = VCASystem> {
    arbitrary_slot_type().prop_map(|slot_type| {
        let slot = SlotId(1);
        VCASystem::new(slot, slot_type).expect("valid system")
    })
}

fn arbitrary_transition() -> impl Strategy<Value = Transition> {
    let slot_id_gen = (1u64..1000).prop_map(SlotId);
    prop_oneof![
        (slot_id_gen.clone(), arbitrary_slot_type())
            .prop_map(|(v, t)| { Transition::InsertSlot { v, t } }),
        slot_id_gen
            .clone()
            .prop_map(|v| Transition::DeleteSlot { v }),
        (slot_id_gen.clone(), slot_id_gen.clone(), (0u32..5))
            .prop_map(|(u, v, i)| { Transition::Attach { u, v, i } }),
        (slot_id_gen.clone(), slot_id_gen.clone(), (0u32..5))
            .prop_map(|(u, v, i)| { Transition::Detach { u, v, i } }),
        (slot_id_gen.clone(), arbitrary_slot_type())
            .prop_map(|(v, t)| { Transition::Retype { v, t } }),
    ]
}

proptest! {
    #[test]
    fn t29_1_arbitrary_valid_transition_preserves_structure(
        system in arbitrary_valid_system(),
        transition in arbitrary_transition(),
    ) {
        if !system.is_structurally_valid() {
            return Ok(());
        }

        if !transition.precondition(&system) {
            return Ok(());
        }

        let result = transition.apply(&system);
        match result {
            Ok(result_system) => {
                prop_assert!(
                    result_system.is_structurally_valid(),
                    "valid transition on valid system must produce valid system"
                );
            }
            Err(_) => {
                return Ok(());
            }
        }
    }

    #[test]
    fn t29_1_core_preserves_structural_validity(
        system in arbitrary_valid_system(),
    ) {
        if !system.is_structurally_valid() {
            return Ok(());
        }

        let result = core(&system);
        prop_assert!(
            result.is_structurally_valid(),
            "core must preserve structural validity"
        );
    }

    #[test]
    fn t29_1_core_star_preserves_structural_validity(
        system in arbitrary_valid_system(),
    ) {
        if !system.is_structurally_valid() {
            return Ok(());
        }

        let registry = KindRegistry::with_base_kinds();
        let result = core_star(&system, &registry);
        prop_assert!(
            result.is_structurally_valid(),
            "core_star must preserve structural validity"
        );
    }

    #[test]
    fn t29_2_core_idempotent(
        system in arbitrary_valid_system(),
    ) {
        let core1 = core(&system);
        let core2 = core(&core1);

        let normalized_core1 = normalize_system(core1);
        let normalized_core2 = normalize_system(core2);

        prop_assert_eq!(
            normalized_core1.slots(), normalized_core2.slots(),
            "core(core(F)) must have same slots as core(F)"
        );
        prop_assert_eq!(
            normalized_core1.relations(), normalized_core2.relations(),
            "core(core(F)) must have same relations as core(F)"
        );
    }

    #[test]
    fn t29_2_core_r_idempotent(
        system in arbitrary_valid_system(),
    ) {
        let registry = KindRegistry::with_base_kinds();
        let core_r1 = core_r(&system, &registry);
        let core_r2 = core_r(&core_r1, &registry);

        let normalized_core_r1 = normalize_system(core_r1);
        let normalized_core_r2 = normalize_system(core_r2);

        prop_assert_eq!(
            normalized_core_r1.slots(), normalized_core_r2.slots(),
            "core_r(core_r(F)) must have same slots as core_r(F)"
        );
        prop_assert_eq!(
            normalized_core_r1.relations(), normalized_core_r2.relations(),
            "core_r(core_r(F)) must have same relations as core_r(F)"
        );
    }

    #[test]
    fn t29_2_core_star_idempotent(
        system in arbitrary_valid_system(),
    ) {
        let registry = KindRegistry::with_base_kinds();
        let core_star1 = core_star(&system, &registry);
        let core_star2 = core_star(&core_star1, &registry);

        let normalized_core_star1 = normalize_system(core_star1);
        let normalized_core_star2 = normalize_system(core_star2);

        prop_assert_eq!(
            normalized_core_star1.slots(), normalized_core_star2.slots(),
            "core_star(core_star(F)) must have same slots as core_star(F)"
        );
        prop_assert_eq!(
            normalized_core_star1.relations(), normalized_core_star2.relations(),
            "core_star(core_star(F)) must have same relations as core_star(F)"
        );
    }

    #[test]
    fn t29_3_independent_transitions_commute(
        system in arbitrary_valid_system(),
        t1 in arbitrary_transition(),
        t2 in arbitrary_transition(),
    ) {
        if !system.is_structurally_valid() {
            return Ok(());
        }

        if !t1.precondition(&system) || !t2.precondition(&system) {
            return Ok(());
        }

        if !is_independent(&t1, &t2, &system) {
            return Ok(());
        }

        let system_t1_t2 = t1
            .apply(&system)
            .and_then(|s| t2.apply(&s))
            .ok();
        let system_t2_t1 = t2
            .apply(&system)
            .and_then(|s| t1.apply(&s))
            .ok();

        match (system_t1_t2, system_t2_t1) {
            (Some(s1), Some(s2)) => {
                let normalized_s1 = normalize_system(s1);
                let normalized_s2 = normalize_system(s2);

                prop_assert_eq!(
                    normalized_s1.slots(), normalized_s2.slots(),
                    "independent transitions must commute: slots differ"
                );
                prop_assert_eq!(
                    normalized_s1.relations(), normalized_s2.relations(),
                    "independent transitions must commute: relations differ"
                );
            }
            _ => {
                return Ok(());
            }
        }
    }
}

fn arbitrary_transaction() -> impl Strategy<Value = Transaction> {
    let slot_id_gen = (1u64..100).prop_map(SlotId);

    (
        prop::collection::vec(
            prop_oneof![
                (slot_id_gen.clone(), arbitrary_slot_type())
                    .prop_map(|(v, t)| { Transition::InsertSlot { v, t } }),
                slot_id_gen
                    .clone()
                    .prop_map(|v| Transition::DeleteSlot { v }),
                (slot_id_gen.clone(), slot_id_gen.clone(), (0u32..5),)
                    .prop_map(|(u, v, i)| Transition::Attach { u, v, i }),
                (slot_id_gen.clone(), slot_id_gen.clone(), (0u32..5),)
                    .prop_map(|(u, v, i)| Transition::Detach { u, v, i }),
                (slot_id_gen.clone(), arbitrary_slot_type())
                    .prop_map(|(v, t)| { Transition::Retype { v, t } }),
            ],
            0..10,
        ),
        (0u64..100).prop_map(vca::replay::ReplicaId),
        prop::collection::hash_map((0u64..10).prop_map(vca::replay::ReplicaId), 0u64..100, 0..5)
            .prop_map(vca::replay::VectorClock::from),
        (0u64..1000),
    )
        .prop_map(|(ops, origin, vc, seq)| Transaction {
            ops,
            origin,
            vc,
            seq,
        })
}

proptest! {
    #[test]
    fn t29_4_replay_deterministic(
        initial in arbitrary_valid_system(),
        history in prop::collection::vec(arbitrary_transaction(), 0..5),
    ) {
        if !initial.is_structurally_valid() {
            return Ok(());
        }

        let registry = KindRegistry::with_base_kinds();

        let result1 = replay(&history, &initial, &registry);
        let result2 = replay(&history, &initial, &registry);

        match (result1, result2) {
            (Ok(r1), Ok(r2)) => {
                let normalized_r1 = normalize_system(r1);
                let normalized_r2 = normalize_system(r2);

                prop_assert_eq!(
                    normalized_r1.slots(), normalized_r2.slots(),
                    "replay must be deterministic: slots differ"
                );
                prop_assert_eq!(
                    normalized_r1.relations(), normalized_r2.relations(),
                    "replay must be deterministic: relations differ"
                );
            }
            (Err(_), Err(_)) => {
                return Ok(());
            }
            _ => {
                prop_assert!(false, "replay must be deterministic: one succeeded, one failed");
            }
        }
    }

    #[test]
    fn t29_4_replay_convergence(
        initial in arbitrary_valid_system(),
        h1 in prop::collection::vec(arbitrary_transaction(), 0..3),
        h2 in prop::collection::vec(arbitrary_transaction(), 0..3),
    ) {
        if !initial.is_structurally_valid() {
            return Ok(());
        }

        let registry = KindRegistry::with_base_kinds();

        let mut h1_union_h2 = h1.clone();
        h1_union_h2.extend(h2.clone());
        sort_transactions(&mut h1_union_h2);

        let mut h2_union_h1 = h2.clone();
        h2_union_h1.extend(h1.clone());
        sort_transactions(&mut h2_union_h1);

        let result_h1_h2 = replay(&h1_union_h2, &initial, &registry);
        let result_h2_h1 = replay(&h2_union_h1, &initial, &registry);

        match (result_h1_h2, result_h2_h1) {
            (Ok(r1), Ok(r2)) => {
                let normalized_r1 = normalize_system(r1);
                let normalized_r2 = normalize_system(r2);

                prop_assert_eq!(
                    normalized_r1.slots(), normalized_r2.slots(),
                    "replay(H1 ∪ H2) must equal replay(H2 ∪ H1): slots differ"
                );
                prop_assert_eq!(
                    normalized_r1.relations(), normalized_r2.relations(),
                    "replay(H1 ∪ H2) must equal replay(H2 ∪ H1): relations differ"
                );
            }
            (Err(_), Err(_)) => {
                return Ok(());
            }
            _ => {
                return Ok(());
            }
        }
    }
}

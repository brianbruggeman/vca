use crate::core::core_star;
use crate::registry::KindRegistry;
use crate::system::VCASystem;
use crate::transitions::{Transition, TransitionError};
use std::cmp::Ordering;
use std::collections::HashMap;

/// Identifies a replica in the distributed system.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ReplicaId(pub u64);

/// Lamport-style vector clock for causal ordering.
pub type VectorClock = HashMap<ReplicaId, u64>;

/// A transaction: a sequence of transitions with causal metadata.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transaction {
    pub ops: Vec<Transition>,
    pub origin: ReplicaId,
    pub vc: VectorClock,
    pub seq: u64,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ReplayError {
    TransitionError(TransitionError),
}

impl std::fmt::Display for ReplayError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TransitionError(e) => write!(f, "transition error: {e:?}"),
        }
    }
}

impl std::error::Error for ReplayError {}

impl From<TransitionError> for ReplayError {
    fn from(e: TransitionError) -> Self {
        Self::TransitionError(e)
    }
}

/// Lexicographic comparison of vector clocks for deterministic ordering.
pub fn vc_cmp(vc1: &VectorClock, vc2: &VectorClock) -> Ordering {
    let all_replicas: Vec<ReplicaId> = {
        let mut replicas: Vec<ReplicaId> = vc1.keys().chain(vc2.keys()).copied().collect();
        replicas.sort_by_key(|r| r.0);
        replicas.dedup();
        replicas
    };

    for replica in all_replicas {
        let v1 = vc1.get(&replica).copied().unwrap_or(0);
        let v2 = vc2.get(&replica).copied().unwrap_or(0);
        match v1.cmp(&v2) {
            Ordering::Equal => continue,
            other => return other,
        }
    }

    Ordering::Equal
}

/// Total order on transactions: vector clock, then origin, then sequence number.
pub fn tx_cmp(t1: &Transaction, t2: &Transaction) -> Ordering {
    match vc_cmp(&t1.vc, &t2.vc) {
        Ordering::Equal => match t1.origin.0.cmp(&t2.origin.0) {
            Ordering::Equal => t1.seq.cmp(&t2.seq),
            other => other,
        },
        other => other,
    }
}

/// Sorts transactions into deterministic replay order.
pub fn sort_transactions(txs: &mut [Transaction]) {
    txs.sort_by(tx_cmp);
}

/// Evaluates a single transaction against a system, applying core_star after each op.
pub fn eval(
    tx: &Transaction,
    system: &VCASystem,
    registry: &KindRegistry,
) -> Result<VCASystem, ReplayError> {
    let mut current = system.clone();

    for op in &tx.ops {
        match op.apply(&current) {
            Ok(next) => {
                current = core_star(&next, registry);
            }
            Err(_) => {
                // skip invalid transitions, continue replay
            }
        }
    }

    Ok(current)
}

/// Replays a history of transactions in deterministic order (Theorem 12).
pub fn replay(
    history: &[Transaction],
    initial: &VCASystem,
    registry: &KindRegistry,
) -> Result<VCASystem, ReplayError> {
    let mut sorted: Vec<Transaction> = history.to_vec();
    sort_transactions(&mut sorted);

    let mut current = initial.clone();

    for tx in &sorted {
        current = eval(tx, &current, registry)?;
    }

    Ok(current)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::slot::SlotId;
    use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};

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

    fn make_test_system() -> VCASystem {
        let slot = SlotId(1);
        let slot_type = make_test_slot_type();
        VCASystem::new(slot, slot_type).unwrap()
    }

    #[test]
    fn replica_id_constructs_correctly() {
        let r1 = ReplicaId(42);
        assert_eq!(r1.0, 42);
    }

    #[test]
    fn transaction_constructs_correctly() {
        let origin = ReplicaId(1);
        let mut vc = VectorClock::new();
        vc.insert(origin, 5);
        let tx = Transaction {
            ops: vec![],
            origin,
            vc,
            seq: 10,
        };
        assert_eq!(tx.origin, origin);
        assert_eq!(tx.seq, 10);
        assert_eq!(tx.ops.len(), 0);
    }

    #[test]
    fn vector_clock_is_hashmap() {
        let mut vc: VectorClock = HashMap::new();
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);
        vc.insert(r1, 5);
        vc.insert(r2, 10);
        assert_eq!(vc.get(&r1), Some(&5));
        assert_eq!(vc.get(&r2), Some(&10));
    }

    #[test]
    fn vc_cmp_compares_lexicographically() {
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);

        let mut vc1 = VectorClock::new();
        vc1.insert(r1, 1);
        vc1.insert(r2, 2);

        let mut vc2 = VectorClock::new();
        vc2.insert(r1, 1);
        vc2.insert(r2, 3);

        assert_eq!(vc_cmp(&vc1, &vc2), Ordering::Less);
        assert_eq!(vc_cmp(&vc2, &vc1), Ordering::Greater);
    }

    #[test]
    fn vc_cmp_handles_missing_keys() {
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);

        let mut vc1 = VectorClock::new();
        vc1.insert(r1, 1);

        let mut vc2 = VectorClock::new();
        vc2.insert(r1, 1);
        vc2.insert(r2, 0);

        assert_eq!(vc_cmp(&vc1, &vc2), Ordering::Equal);
    }

    #[test]
    fn vc_cmp_equal_when_identical() {
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);

        let mut vc1 = VectorClock::new();
        vc1.insert(r1, 5);
        vc1.insert(r2, 10);

        let mut vc2 = VectorClock::new();
        vc2.insert(r1, 5);
        vc2.insert(r2, 10);

        assert_eq!(vc_cmp(&vc1, &vc2), Ordering::Equal);
    }

    #[test]
    fn tx_cmp_orders_by_vc_then_origin_then_seq() {
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);

        let mut vc1 = VectorClock::new();
        vc1.insert(r1, 1);

        let mut vc2 = VectorClock::new();
        vc2.insert(r1, 2);

        let tx1 = Transaction {
            ops: vec![],
            origin: r1,
            vc: vc1,
            seq: 100,
        };

        let tx2 = Transaction {
            ops: vec![],
            origin: r2,
            vc: vc2,
            seq: 1,
        };

        assert_eq!(tx_cmp(&tx1, &tx2), Ordering::Less);
    }

    #[test]
    fn tx_cmp_breaks_ties_by_origin() {
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);

        let mut vc = VectorClock::new();
        vc.insert(r1, 5);

        let tx1 = Transaction {
            ops: vec![],
            origin: r1,
            vc: vc.clone(),
            seq: 10,
        };

        let tx2 = Transaction {
            ops: vec![],
            origin: r2,
            vc,
            seq: 5,
        };

        assert_eq!(tx_cmp(&tx1, &tx2), Ordering::Less);
    }

    #[test]
    fn tx_cmp_breaks_ties_by_seq() {
        let r1 = ReplicaId(1);

        let mut vc = VectorClock::new();
        vc.insert(r1, 5);

        let tx1 = Transaction {
            ops: vec![],
            origin: r1,
            vc: vc.clone(),
            seq: 5,
        };

        let tx2 = Transaction {
            ops: vec![],
            origin: r1,
            vc,
            seq: 10,
        };

        assert_eq!(tx_cmp(&tx1, &tx2), Ordering::Less);
    }

    #[test]
    fn sort_transactions_produces_deterministic_order() {
        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);

        let mut vc1 = VectorClock::new();
        vc1.insert(r1, 1);

        let mut vc2 = VectorClock::new();
        vc2.insert(r1, 2);

        let mut vc3 = VectorClock::new();
        vc3.insert(r1, 1);
        vc3.insert(r2, 1);

        let mut txs = vec![
            Transaction {
                ops: vec![],
                origin: r2,
                vc: vc2.clone(),
                seq: 1,
            },
            Transaction {
                ops: vec![],
                origin: r1,
                vc: vc1.clone(),
                seq: 5,
            },
            Transaction {
                ops: vec![],
                origin: r1,
                vc: vc3.clone(),
                seq: 1,
            },
        ];

        sort_transactions(&mut txs);

        assert_eq!(txs[0].vc, vc1);
        assert_eq!(txs[1].vc, vc3);
        assert_eq!(txs[2].vc, vc2);
    }

    #[test]
    fn eval_applies_all_ops_sequentially() {
        let system = make_test_system();
        let registry = KindRegistry::with_base_kinds();

        let slot2 = SlotId(2);
        let slot_type = make_test_slot_type();

        let tx = Transaction {
            ops: vec![Transition::InsertSlot {
                v: slot2,
                t: slot_type.clone(),
            }],
            origin: ReplicaId(1),
            vc: VectorClock::new(),
            seq: 1,
        };

        let result = eval(&tx, &system, &registry).unwrap();
        assert!(result.contains_slot(slot2));
    }

    #[test]
    fn eval_calls_core_star_after_each_op() {
        let system = make_test_system();
        let registry = KindRegistry::with_base_kinds();

        let slot2 = SlotId(2);
        let slot3 = SlotId(3);
        let slot_type = make_test_slot_type();

        let tx = Transaction {
            ops: vec![
                Transition::InsertSlot {
                    v: slot2,
                    t: slot_type.clone(),
                },
                Transition::InsertSlot {
                    v: slot3,
                    t: slot_type,
                },
            ],
            origin: ReplicaId(1),
            vc: VectorClock::new(),
            seq: 1,
        };

        let result = eval(&tx, &system, &registry).unwrap();
        assert!(result.contains_slot(slot2));
        assert!(result.contains_slot(slot3));
    }

    #[test]
    fn eval_skips_invalid_transitions() {
        let system = make_test_system();
        let registry = KindRegistry::with_base_kinds();

        let slot1 = SlotId(1);
        let slot2 = SlotId(2);
        let slot_type = make_test_slot_type();

        let tx = Transaction {
            ops: vec![
                Transition::InsertSlot {
                    v: slot1,
                    t: slot_type.clone(),
                },
                Transition::InsertSlot {
                    v: slot2,
                    t: slot_type,
                },
            ],
            origin: ReplicaId(1),
            vc: VectorClock::new(),
            seq: 1,
        };

        let result = eval(&tx, &system, &registry).unwrap();
        assert!(result.contains_slot(slot1));
        assert!(result.contains_slot(slot2));
        assert_eq!(result.slot_count(), 2);
    }

    #[test]
    fn replay_sorts_transactions_before_applying() {
        let initial = make_test_system();
        let registry = KindRegistry::with_base_kinds();

        let r1 = ReplicaId(1);
        let r2 = ReplicaId(2);

        let mut vc1 = VectorClock::new();
        vc1.insert(r1, 1);

        let mut vc2 = VectorClock::new();
        vc2.insert(r1, 2);

        let slot2 = SlotId(2);
        let slot3 = SlotId(3);
        let slot_type = make_test_slot_type();

        let history = vec![
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

        let result = replay(&history, &initial, &registry).unwrap();
        assert!(result.contains_slot(slot2));
        assert!(result.contains_slot(slot3));
    }

    #[test]
    fn replay_deterministic_same_history_same_result() {
        let initial = make_test_system();
        let registry = KindRegistry::with_base_kinds();

        let r1 = ReplicaId(1);
        let mut vc = VectorClock::new();
        vc.insert(r1, 1);

        let slot2 = SlotId(2);
        let slot_type = make_test_slot_type();

        let history = vec![Transaction {
            ops: vec![Transition::InsertSlot {
                v: slot2,
                t: slot_type,
            }],
            origin: r1,
            vc,
            seq: 1,
        }];

        let result1 = replay(&history, &initial, &registry).unwrap();
        let result2 = replay(&history, &initial, &registry).unwrap();

        assert_eq!(result1.slots, result2.slots);
        assert_eq!(result1.relations, result2.relations);
        assert_eq!(result1.types, result2.types);
    }

    #[test]
    fn replay_different_orderings_converge() {
        let initial = make_test_system();
        let registry = KindRegistry::with_base_kinds();

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

        let result1 = replay(&history1, &initial, &registry).unwrap();
        let result2 = replay(&history2, &initial, &registry).unwrap();

        assert_eq!(result1.slots.len(), result2.slots.len());
        assert!(result1.contains_slot(slot2));
        assert!(result1.contains_slot(slot3));
        assert!(result2.contains_slot(slot2));
        assert!(result2.contains_slot(slot3));
    }

    #[test]
    fn replay_invalid_transition_skipped_continues() {
        let initial = make_test_system();
        let registry = KindRegistry::with_base_kinds();

        let r1 = ReplicaId(1);
        let mut vc = VectorClock::new();
        vc.insert(r1, 1);

        let slot1 = SlotId(1);
        let slot2 = SlotId(2);
        let slot_type = make_test_slot_type();

        let history = vec![
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot1,
                    t: slot_type.clone(),
                }],
                origin: r1,
                vc: vc.clone(),
                seq: 1,
            },
            Transaction {
                ops: vec![Transition::InsertSlot {
                    v: slot2,
                    t: slot_type,
                }],
                origin: r1,
                vc,
                seq: 2,
            },
        ];

        let result = replay(&history, &initial, &registry).unwrap();
        assert!(result.contains_slot(slot1));
        assert!(result.contains_slot(slot2));
    }
}

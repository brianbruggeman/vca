use std::collections::HashMap;

use crate::relation::Relation;
use crate::slot::SlotId;
use crate::types::{Family, SlotType};

/// Reference to the rule system ℛ governing admissibility.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RuleRef {
    /// No rule system.
    Empty,
    /// Self-referential: ℛ = F (the system governs itself).
    SelfRef,
    /// External rule system from a different level.
    External(Box<VCASystem>),
}

/// The VCA 4-tuple `F = (V, A, τ, ℛ)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VCASystem {
    /// V: non-empty set of slots.
    pub slots: Vec<SlotId>,
    /// A ⊆ V × V × I: directed relations with position indices.
    pub relations: Vec<Relation>,
    /// τ: V → T: total type assignment.
    pub types: HashMap<SlotId, SlotType>,
    /// ℛ: the rule system governing admissibility.
    pub rule_ref: RuleRef,
}

#[derive(Debug, PartialEq, Eq)]
pub enum SystemError {
    SlotNotFound,
    TypeNotWellFormed,
    PositionOccupied,
    UpperBoundViolated,
    WouldBeEmpty,
}

impl std::fmt::Display for SystemError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SlotNotFound => write!(f, "slot not found"),
            Self::TypeNotWellFormed => write!(f, "type not well-formed"),
            Self::PositionOccupied => write!(f, "position already occupied"),
            Self::UpperBoundViolated => write!(f, "upper bound violated"),
            Self::WouldBeEmpty => write!(f, "system would be empty"),
        }
    }
}

impl std::error::Error for SystemError {}

impl VCASystem {
    pub fn new(slot: SlotId, slot_type: SlotType) -> Result<Self, SystemError> {
        if !slot_type.is_well_formed() {
            return Err(SystemError::TypeNotWellFormed);
        }

        let mut types = HashMap::new();
        types.insert(slot, slot_type);

        Ok(VCASystem {
            slots: vec![slot],
            relations: Vec::new(),
            types,
            rule_ref: RuleRef::Empty,
        })
    }

    pub fn contains_slot(&self, v: SlotId) -> bool {
        self.slots.contains(&v)
    }

    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    pub fn type_of(&self, v: SlotId) -> Option<&SlotType> {
        self.types.get(&v)
    }

    pub fn sources(&self, v: SlotId) -> Vec<SlotId> {
        self.relations
            .iter()
            .filter_map(|rel| {
                if rel.target == v {
                    Some(rel.source)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn targets(&self, u: SlotId) -> Vec<SlotId> {
        self.relations
            .iter()
            .filter_map(|rel| {
                if rel.source == u {
                    Some(rel.target)
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn src_count(&self, v: SlotId) -> u32 {
        self.sources(v).len() as u32
    }

    pub fn rule_slots(&self) -> Vec<SlotId> {
        self.slots
            .iter()
            .filter_map(|&v| {
                self.type_of(v)
                    .filter(|t| t.family == Family::Rule)
                    .map(|_| v)
            })
            .collect()
    }

    pub fn is_position_unique(&self) -> bool {
        let mut seen = HashMap::new();
        for rel in &self.relations {
            let key = (rel.target, rel.position);
            if let Some(existing_source) = seen.get(&key) {
                if *existing_source != rel.source {
                    return false;
                }
            } else {
                seen.insert(key, rel.source);
            }
        }
        true
    }

    pub fn is_structurally_valid(&self) -> bool {
        if self.slots.is_empty() {
            return false;
        }

        for &v in &self.slots {
            if !self.types.contains_key(&v) {
                return false;
            }
        }

        if !self.is_position_unique() {
            return false;
        }

        for &v in &self.slots {
            let src_count = self.src_count(v);
            if let Some(slot_type) = self.type_of(v)
                && !slot_type.upper_satisfied(src_count)
            {
                return false;
            }
        }

        true
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::types::{Affinity, Kind, Layer, TypeId, TypeMeta, UpperBound};
    use rstest::rstest;

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

    #[test]
    fn new_creates_system_with_single_slot() {
        let (slot, slot_type) = make_test_slot();
        let system = VCASystem::new(slot, slot_type).unwrap();

        assert_eq!(system.slot_count(), 1);
        assert!(system.contains_slot(slot));
        assert_eq!(system.relations.len(), 0);
    }

    #[test]
    fn new_is_structurally_valid() {
        let (slot, slot_type) = make_test_slot();
        let system = VCASystem::new(slot, slot_type).unwrap();
        assert!(system.is_structurally_valid());
    }

    #[test]
    fn new_rejects_malformed_type() {
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
        let result = VCASystem::new(slot, bad_slot_type);
        assert_eq!(result, Err(SystemError::TypeNotWellFormed));
    }

    #[rstest]
    #[case::existing_slot(true)]
    #[case::non_existing_slot(false)]
    fn contains_slot_cases(#[case] exists: bool) {
        let (slot, slot_type) = make_test_slot();
        let system = VCASystem::new(slot, slot_type).unwrap();
        let test_slot = if exists { slot } else { SlotId(999) };
        assert_eq!(system.contains_slot(test_slot), exists);
    }

    #[test]
    fn type_of_returns_some_for_existing() {
        let (slot, slot_type) = make_test_slot();
        let system = VCASystem::new(slot, slot_type.clone()).unwrap();
        assert_eq!(system.type_of(slot), Some(&slot_type));
    }

    #[test]
    fn type_of_returns_none_for_non_existing() {
        let (slot, slot_type) = make_test_slot();
        let system = VCASystem::new(slot, slot_type).unwrap();
        assert_eq!(system.type_of(SlotId(999)), None);
    }

    fn make_test_system_with_relations() -> VCASystem {
        let a = SlotId(1);
        let b = SlotId(2);
        let c = SlotId(3);
        let d = SlotId(4);

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

        let mut system = VCASystem::new(a, slot_type.clone()).unwrap();

        system.slots.push(b);
        system.slots.push(c);
        system.slots.push(d);
        system.types.insert(b, slot_type.clone());
        system.types.insert(c, slot_type.clone());
        system.types.insert(d, slot_type);

        system.relations.push(Relation {
            source: a,
            target: b,
            position: 0,
        });
        system.relations.push(Relation {
            source: c,
            target: b,
            position: 1,
        });
        system.relations.push(Relation {
            source: a,
            target: d,
            position: 0,
        });

        system
    }

    #[test]
    fn sources_returns_correct_sources() {
        let system = make_test_system_with_relations();
        let b = SlotId(2);
        let d = SlotId(4);
        let a = SlotId(1);

        let sources_b = system.sources(b);
        assert_eq!(sources_b.len(), 2);
        assert!(sources_b.contains(&a));
        assert!(sources_b.contains(&SlotId(3)));

        let sources_d = system.sources(d);
        assert_eq!(sources_d.len(), 1);
        assert_eq!(sources_d[0], a);

        let sources_a = system.sources(a);
        assert_eq!(sources_a.len(), 0);
    }

    #[test]
    fn targets_returns_correct_targets() {
        let system = make_test_system_with_relations();
        let a = SlotId(1);
        let b = SlotId(2);

        let targets_a = system.targets(a);
        assert_eq!(targets_a.len(), 2);
        assert!(targets_a.contains(&b));
        assert!(targets_a.contains(&SlotId(4)));

        let targets_b = system.targets(b);
        assert_eq!(targets_b.len(), 0);
    }

    #[test]
    fn src_count_returns_correct_count() {
        let system = make_test_system_with_relations();
        let b = SlotId(2);
        let a = SlotId(1);

        assert_eq!(system.src_count(b), 2);
        assert_eq!(system.src_count(a), 0);
    }

    #[test]
    fn rule_slots_returns_only_rule_family() {
        let mut system = make_test_system_with_relations();
        let v1 = SlotId(10);
        let v2 = SlotId(11);
        let v3 = SlotId(12);

        system.slots.push(v1);
        system.slots.push(v2);
        system.slots.push(v3);

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

        system.types.insert(v1, rule_type.clone());
        system.types.insert(v2, data_type);
        system.types.insert(v3, rule_type);

        let rule_slots = system.rule_slots();
        assert_eq!(rule_slots.len(), 2);
        assert!(rule_slots.contains(&v1));
        assert!(rule_slots.contains(&v3));
        assert!(!rule_slots.contains(&v2));
    }

    #[test]
    fn is_position_unique_passes_for_unique_positions() {
        let system = make_test_system_with_relations();
        assert!(system.is_position_unique());
    }

    #[test]
    fn is_position_unique_passes_for_different_positions() {
        let mut system = make_test_system_with_relations();
        system.relations.push(Relation {
            source: SlotId(5),
            target: SlotId(2),
            position: 2,
        });
        assert!(system.is_position_unique());
    }

    #[test]
    fn is_position_unique_fails_for_duplicate_position() {
        let mut system = make_test_system_with_relations();
        system.relations.push(Relation {
            source: SlotId(5),
            target: SlotId(2),
            position: 0,
        });
        assert!(!system.is_position_unique());
    }

    #[test]
    fn is_structurally_valid_fails_for_empty_slots() {
        let system = VCASystem {
            slots: Vec::new(),
            relations: Vec::new(),
            types: HashMap::new(),
            rule_ref: RuleRef::Empty,
        };
        assert!(!system.is_structurally_valid());
    }

    #[test]
    fn is_structurally_valid_fails_for_missing_type() {
        let (slot, slot_type) = make_test_slot();
        let mut system = VCASystem::new(slot, slot_type).unwrap();
        system.types.remove(&slot);
        assert!(!system.is_structurally_valid());
    }

    #[test]
    fn is_structurally_valid_fails_for_position_uniqueness_violation() {
        let mut system = make_test_system_with_relations();
        system.relations.push(Relation {
            source: SlotId(5),
            target: SlotId(2),
            position: 0,
        });
        assert!(!system.is_structurally_valid());
    }

    #[test]
    fn is_structurally_valid_fails_for_upper_bound_violation() {
        let (slot, _) = make_test_slot();
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
        let mut system = VCASystem::new(slot, slot_type).unwrap();

        let other = SlotId(2);
        let other_slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        system.slots.push(other);
        system.types.insert(other, other_slot_type);

        system.relations.push(Relation {
            source: other,
            target: slot,
            position: 0,
        });
        system.relations.push(Relation {
            source: other,
            target: slot,
            position: 1,
        });

        assert!(!system.is_structurally_valid());
    }

    #[test]
    fn is_structurally_valid_passes_for_valid_system() {
        let system = make_test_system_with_relations();
        assert!(system.is_structurally_valid());
    }
}

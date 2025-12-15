use crate::admissibility::is_admissible;
use crate::system::VCASystem;

pub fn all_admissible(system: &VCASystem) -> bool {
    system
        .relations
        .iter()
        .all(|rel| is_admissible(system, rel))
}

pub fn is_coherent(system: &VCASystem) -> bool {
    if !system.is_structurally_valid() {
        return false;
    }

    if !all_admissible(system) {
        return false;
    }

    match &system.rule_ref {
        crate::system::RuleRef::Empty => true,
        crate::system::RuleRef::SelfRef => true,
        crate::system::RuleRef::External(external) => is_coherent(external),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::relation::Relation;
    use crate::slot::SlotId;
    use crate::system::RuleRef;
    use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};

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
    fn all_admissible_returns_true_for_empty_relations() {
        let (slot, slot_type) = make_test_slot();
        let system = VCASystem::new(slot, slot_type).unwrap();
        assert!(all_admissible(&system));
    }

    #[test]
    fn all_admissible_returns_true_when_all_admissible() {
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

        let relation = Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        };
        system.relations.push(relation);

        assert!(all_admissible(&system));
    }

    #[test]
    fn all_admissible_returns_false_when_one_inadmissible() {
        let rule_slot = SlotId(1);
        let data_slot = SlotId(2);

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

        let relation = Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        };
        system.relations.push(relation);

        assert!(!all_admissible(&system));
    }

    #[test]
    fn is_coherent_with_valid_and_admissible_and_empty_rule_ref() {
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
        system.rule_ref = RuleRef::Empty;

        let relation = Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        };
        system.relations.push(relation);

        assert!(is_coherent(&system));
    }

    #[test]
    fn is_coherent_with_valid_and_admissible_and_self_ref() {
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

        let relation = Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        };
        system.relations.push(relation);

        assert!(is_coherent(&system));
    }

    #[test]
    fn is_coherent_returns_false_when_structurally_invalid() {
        let system = VCASystem {
            slots: Vec::new(),
            relations: Vec::new(),
            types: std::collections::HashMap::new(),
            rule_ref: RuleRef::Empty,
        };
        assert!(!is_coherent(&system));
    }

    #[test]
    fn is_coherent_returns_false_when_has_inadmissible_relations() {
        let rule_slot = SlotId(1);
        let data_slot = SlotId(2);

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
        system.rule_ref = RuleRef::Empty;

        let relation = Relation {
            source: data_slot,
            target: data_slot,
            position: 0,
        };
        system.relations.push(relation);

        assert!(!is_coherent(&system));
    }

    #[test]
    fn is_coherent_with_external_rule_ref() {
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

        let mut external_system = VCASystem::new(rule_slot, rule_type).unwrap();
        external_system.rule_ref = RuleRef::Empty;

        let mut system = VCASystem::new(data_slot, data_type).unwrap();
        system.rule_ref = RuleRef::External(Box::new(external_system));

        assert!(is_coherent(&system));
    }

    #[test]
    fn is_coherent_with_incoherent_external_rule_ref() {
        let rule_slot = SlotId(1);
        let data_slot = SlotId(2);

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

        let mut external_system = VCASystem::new(rule_slot, rule_type).unwrap();
        let external_data = SlotId(3);
        external_system.slots.push(external_data);
        external_system.types.insert(
            external_data,
            SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(3),
                meta: TypeMeta::None,
            },
        );
        external_system.relations.push(Relation {
            source: external_data,
            target: external_data,
            position: 0,
        });
        external_system.rule_ref = RuleRef::Empty;

        let mut system = VCASystem::new(data_slot, data_type).unwrap();
        system.rule_ref = RuleRef::External(Box::new(external_system));

        assert!(!is_coherent(&system));
    }
}

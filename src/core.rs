use crate::admissibility::is_admissible;
use crate::registry::KindRegistry;
use crate::slot::SlotId;
use crate::system::VCASystem;
use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};
use std::collections::{HashMap, HashSet};

/// Removes inadmissible relations, preserving slots and types.
pub fn core(system: &VCASystem) -> VCASystem {
    let admissible_relations: Vec<_> = system
        .relations
        .iter()
        .filter(|rel| is_admissible(system, rel))
        .copied()
        .collect();

    VCASystem {
        slots: system.slots.clone(),
        relations: admissible_relations,
        types: system.types.clone(),
        rule_ref: system.rule_ref.clone(),
    }
}

fn is_valid_rule_locus(system: &VCASystem, registry: &KindRegistry, locus: SlotId) -> bool {
    let Some(slot_type) = system.type_of(locus) else {
        return false;
    };

    if slot_type.family != Family::Rule {
        return true;
    }

    registry.lookup(slot_type.kind).is_some()
}

/// Removes rule slots with unregistered kinds, preserving valid loci.
pub fn core_r(system: &VCASystem, registry: &KindRegistry) -> VCASystem {
    let valid_loci: Vec<SlotId> = system
        .slots
        .iter()
        .filter(|&&locus| is_valid_rule_locus(system, registry, locus))
        .copied()
        .collect();

    let loci_set: HashSet<SlotId> = valid_loci.iter().copied().collect();

    let final_loci = if valid_loci.is_empty() {
        let default_locus = SlotId(0);
        vec![default_locus]
    } else {
        valid_loci
    };

    let final_loci_set: HashSet<SlotId> = final_loci.iter().copied().collect();

    let filtered_relations: Vec<_> = system
        .relations
        .iter()
        .filter(|rel| final_loci_set.contains(&rel.source) && final_loci_set.contains(&rel.target))
        .copied()
        .collect();

    let mut types = HashMap::new();

    for &locus in &final_loci {
        if loci_set.contains(&locus) {
            if let Some(slot_type) = system.type_of(locus) {
                types.insert(locus, slot_type.clone());
            }
        } else {
            let default_slot_type = SlotType {
                family: Family::Rule,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Top,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(0),
                meta: TypeMeta::None,
            };
            types.insert(locus, default_slot_type);
        }
    }

    VCASystem {
        slots: final_loci,
        relations: filtered_relations,
        types,
        rule_ref: system.rule_ref.clone(),
    }
}

/// Composes `core(core_r(F))` — produces a coherent system from any input (Theorem 9).
pub fn core_star(system: &VCASystem, registry: &KindRegistry) -> VCASystem {
    core(&core_r(system, registry))
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::relation::Relation;

    fn make_test_system() -> VCASystem {
        let locus = SlotId(1);
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
        VCASystem::new(locus, slot_type).unwrap()
    }

    fn make_system_with_rule(kind: Kind) -> VCASystem {
        let rule_locus = SlotId(1);
        let data_locus = SlotId(2);

        let rule_type = SlotType {
            family: Family::Rule,
            kind,
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

        let mut system = VCASystem::new(rule_locus, rule_type).unwrap();

        system.slots.push(data_locus);
        system.types.insert(data_locus, data_type);

        system
    }

    #[test]
    fn core_with_all_admissible_relations_unchanged() {
        let rule_locus = SlotId(1);
        let data_locus = SlotId(2);

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

        let mut system = VCASystem::new(rule_locus, rule_type).unwrap();

        system.slots.push(data_locus);
        system.types.insert(data_locus, data_type);

        let relation = Relation {
            source: data_locus,
            target: data_locus,
            position: 0,
        };
        system.relations.push(relation);

        let result = core(&system);
        assert_eq!(result.relations.len(), 1);
        assert_eq!(result.slots, system.slots);
        assert_eq!(result.types, system.types);
    }

    #[test]
    fn core_with_one_inadmissible_relation_removes_it() {
        let rule_locus = SlotId(1);
        let data_locus = SlotId(2);

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

        let mut system = VCASystem::new(rule_locus, rule_type).unwrap();

        system.slots.push(data_locus);
        system.types.insert(data_locus, data_type);

        let relation = Relation {
            source: data_locus,
            target: data_locus,
            position: 0,
        };
        system.relations.push(relation);

        let result = core(&system);
        assert_eq!(result.relations.len(), 0);
        assert_eq!(result.slots, system.slots);
    }

    #[test]
    fn core_with_all_inadmissible_relations_has_empty_a() {
        let rule_locus = SlotId(1);
        let data1 = SlotId(2);
        let data2 = SlotId(3);

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

        let mut system = VCASystem::new(rule_locus, rule_type).unwrap();

        system.slots.push(data1);
        system.slots.push(data2);
        system.types.insert(data1, data_type.clone());
        system.types.insert(data2, data_type);

        system.relations.push(Relation {
            source: data1,
            target: data2,
            position: 0,
        });
        system.relations.push(Relation {
            source: data2,
            target: data1,
            position: 0,
        });

        let result = core(&system);
        assert_eq!(result.relations.len(), 0);
        assert_eq!(result.slots, system.slots);
    }

    #[test]
    fn core_preserves_loci_types() {
        let system = make_test_system();
        let result = core(&system);

        assert_eq!(result.slots, system.slots);
        assert_eq!(result.types, system.types);
    }

    #[test]
    fn core_r_with_all_valid_rule_loci_unchanged() {
        let system = make_system_with_rule(Kind::Any);
        let registry = KindRegistry::with_base_kinds();

        let result = core_r(&system, &registry);

        assert_eq!(result.slots.len(), system.slots.len());
        assert!(result.slots.contains(&SlotId(1)));
        assert!(result.slots.contains(&SlotId(2)));
    }

    #[test]
    fn core_r_removes_rule_locus_with_unknown_kind() {
        let system = make_system_with_rule(Kind::Top);
        let registry = KindRegistry::with_base_kinds();

        let result = core_r(&system, &registry);

        assert_eq!(result.slots.len(), 1);
        assert!(!result.slots.contains(&SlotId(1)));
        assert!(result.slots.contains(&SlotId(2)));
    }

    #[test]
    fn core_r_non_rule_loci_unaffected() {
        let system = make_system_with_rule(Kind::Top);
        let registry = KindRegistry::with_base_kinds();

        let result = core_r(&system, &registry);

        assert!(result.slots.contains(&SlotId(2)));
        assert_eq!(result.type_of(SlotId(2)), system.type_of(SlotId(2)));
    }

    #[test]
    fn core_r_if_all_loci_removed_default_rule_added() {
        let rule_locus = SlotId(1);
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
        let system = VCASystem::new(rule_locus, rule_type).unwrap();
        let registry = KindRegistry::with_base_kinds();

        let result = core_r(&system, &registry);

        assert_eq!(result.slots.len(), 1);
        assert_eq!(result.slots[0], SlotId(0));
        assert_eq!(
            result.type_of(SlotId(0)),
            Some(&SlotType {
                family: Family::Rule,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Top,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(0),
                meta: TypeMeta::None,
            })
        );
    }

    #[test]
    fn core_r_removes_relations_involving_removed_loci() {
        let rule_locus = SlotId(1);
        let data_locus = SlotId(2);

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

        let mut system = VCASystem::new(rule_locus, rule_type).unwrap();

        system.slots.push(data_locus);
        system.types.insert(data_locus, data_type);

        system.relations.push(Relation {
            source: rule_locus,
            target: data_locus,
            position: 0,
        });
        system.relations.push(Relation {
            source: data_locus,
            target: rule_locus,
            position: 0,
        });

        let registry = KindRegistry::with_base_kinds();
        let result = core_r(&system, &registry);

        assert_eq!(result.relations.len(), 0);
    }

    #[test]
    fn core_star_equivalent_to_core_core_r() {
        let rule_locus = SlotId(1);
        let data_locus = SlotId(2);

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

        let mut system = VCASystem::new(rule_locus, rule_type).unwrap();

        system.slots.push(data_locus);
        system.types.insert(data_locus, data_type);

        system.relations.push(Relation {
            source: data_locus,
            target: data_locus,
            position: 0,
        });

        let registry = KindRegistry::with_base_kinds();

        let result_star = core_star(&system, &registry);
        let result_manual = core(&core_r(&system, &registry));

        assert_eq!(result_star.slots, result_manual.slots);
        assert_eq!(result_star.relations, result_manual.relations);
    }

    #[test]
    fn core_star_result_is_coherent() {
        use crate::coherence::is_coherent;

        let rule_locus = SlotId(1);
        let data_locus = SlotId(2);

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

        let mut system = VCASystem::new(rule_locus, rule_type).unwrap();

        system.slots.push(data_locus);
        system.types.insert(data_locus, data_type);

        system.relations.push(Relation {
            source: data_locus,
            target: data_locus,
            position: 0,
        });

        let registry = KindRegistry::with_base_kinds();
        let result = core_star(&system, &registry);

        assert!(is_coherent(&result));
    }

    #[test]
    fn core_star_is_idempotent() {
        let rule_locus = SlotId(1);
        let data_locus = SlotId(2);

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

        let mut system = VCASystem::new(rule_locus, rule_type).unwrap();

        system.slots.push(data_locus);
        system.types.insert(data_locus, data_type);

        system.relations.push(Relation {
            source: data_locus,
            target: data_locus,
            position: 0,
        });

        let registry = KindRegistry::with_base_kinds();

        let result1 = core_star(&system, &registry);
        let result2 = core_star(&result1, &registry);

        assert_eq!(result1.slots, result2.slots);
        assert_eq!(result1.relations, result2.relations);
    }
}

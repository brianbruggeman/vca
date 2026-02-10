use crate::registry::KindRegistry;
use crate::system::VCASystem;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Level {
    L0,
    L1,
    L2,
    LN(u32),
}

impl Level {
    pub fn is_tractable(&self) -> bool {
        matches!(self, Level::L0 | Level::L1 | Level::L2)
    }
}

pub fn system_level(system: &VCASystem, registry: &KindRegistry) -> Level {
    let rule_slots = system.rule_slots();

    if rule_slots.is_empty() {
        return Level::L0;
    }

    let mut max_level = Level::L0;

    for &slot in &rule_slots {
        if let Some(ltype) = system.type_of(slot)
            && let Some((_, level)) = registry.lookup(ltype.kind)
        {
            max_level = match (max_level, level) {
                (Level::LN(n1), Level::LN(n2)) => Level::LN(n1.max(n2)),
                (Level::LN(_), _) => max_level,
                (_, Level::LN(_)) => level,
                (Level::L2, _) | (_, Level::L2) => Level::L2,
                (Level::L1, _) | (_, Level::L1) => Level::L1,
                (Level::L0, Level::L0) => Level::L0,
            };
        }
    }

    max_level
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::slot::SlotId;
    use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};

    #[test]
    fn l0_is_tractable() {
        assert!(Level::L0.is_tractable());
    }

    #[test]
    fn l1_is_tractable() {
        assert!(Level::L1.is_tractable());
    }

    #[test]
    fn l2_is_tractable() {
        assert!(Level::L2.is_tractable());
    }

    #[test]
    fn ln3_is_not_tractable() {
        assert!(!Level::LN(3).is_tractable());
    }

    #[test]
    fn ln100_is_not_tractable() {
        assert!(!Level::LN(100).is_tractable());
    }

    fn make_test_system_with_rule(kind: Kind) -> VCASystem {
        let locus = SlotId(1);
        let slot_type = SlotType {
            family: Family::Rule,
            kind,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        VCASystem::new(locus, slot_type).unwrap()
    }

    #[test]
    fn system_with_only_l0_rules_has_level_l0() {
        let registry = KindRegistry::with_base_kinds();
        let system = make_test_system_with_rule(Kind::Any);
        assert_eq!(system_level(&system, &registry), Level::L0);
    }

    #[test]
    fn system_with_l0_and_l1_rules_has_level_l1() {
        let mut registry = KindRegistry::with_base_kinds();
        registry.register(
            Kind::Top,
            Box::new(crate::admissibility::InterpretAny),
            Level::L1,
        );

        let mut system = make_test_system_with_rule(Kind::Any);
        let l1_locus = SlotId(2);
        let l1_type = SlotType {
            family: Family::Rule,
            kind: Kind::Top,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        system.slots.push(l1_locus);
        system.types.insert(l1_locus, l1_type);

        assert_eq!(system_level(&system, &registry), Level::L1);
    }

    #[test]
    fn system_with_l2_rule_has_level_l2() {
        let mut registry = KindRegistry::with_base_kinds();
        registry.register(
            Kind::Bot,
            Box::new(crate::admissibility::InterpretAny),
            Level::L2,
        );

        let mut system = make_test_system_with_rule(Kind::Any);
        let l2_locus = SlotId(2);
        let l2_type = SlotType {
            family: Family::Rule,
            kind: Kind::Bot,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        system.slots.push(l2_locus);
        system.types.insert(l2_locus, l2_type);

        assert_eq!(system_level(&system, &registry), Level::L2);
    }

    #[test]
    fn system_with_ln_rule_has_level_ln() {
        let mut registry = KindRegistry::with_base_kinds();
        registry.register(
            Kind::Top,
            Box::new(crate::admissibility::InterpretAny),
            Level::LN(3),
        );

        let mut system = make_test_system_with_rule(Kind::Any);
        let ln_locus = SlotId(2);
        let ln_type = SlotType {
            family: Family::Rule,
            kind: Kind::Top,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        system.slots.push(ln_locus);
        system.types.insert(ln_locus, ln_type);

        assert_eq!(system_level(&system, &registry), Level::LN(3));
    }

    #[test]
    fn system_with_multiple_ln_rules_has_max_ln() {
        let mut registry = KindRegistry::with_base_kinds();
        registry.register(
            Kind::Top,
            Box::new(crate::admissibility::InterpretAny),
            Level::LN(3),
        );
        registry.register(
            Kind::Bot,
            Box::new(crate::admissibility::InterpretAny),
            Level::LN(5),
        );

        let mut system = make_test_system_with_rule(Kind::Any);
        let ln3_locus = SlotId(2);
        let ln3_type = SlotType {
            family: Family::Rule,
            kind: Kind::Top,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        system.slots.push(ln3_locus);
        system.types.insert(ln3_locus, ln3_type);

        let ln5_locus = SlotId(3);
        let ln5_type = SlotType {
            family: Family::Rule,
            kind: Kind::Bot,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(3),
            meta: TypeMeta::None,
        };
        system.slots.push(ln5_locus);
        system.types.insert(ln5_locus, ln5_type);

        assert_eq!(system_level(&system, &registry), Level::LN(5));
    }

    #[test]
    fn system_with_no_rules_has_level_l0() {
        let registry = KindRegistry::with_base_kinds();
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
        let system = VCASystem::new(locus, slot_type).unwrap();
        assert_eq!(system_level(&system, &registry), Level::L0);
    }
}

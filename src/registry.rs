use crate::admissibility::{
    InterpretAny, InterpretEq, InterpretNone, InterpretPatternMatch, Interpretation,
};
use crate::stratification::Level;
use crate::types::Kind;
use std::collections::HashMap;

/// Maps rule kinds to their interpretation functions and stratification levels.
pub struct KindRegistry {
    interpretations: HashMap<Kind, Box<dyn Interpretation>>,
    levels: HashMap<Kind, Level>,
}

impl KindRegistry {
    pub fn new() -> Self {
        Self {
            interpretations: HashMap::new(),
            levels: HashMap::new(),
        }
    }

    pub fn with_base_kinds() -> Self {
        let mut registry = Self::new();

        registry.register(Kind::Any, Box::new(InterpretAny), Level::L0);

        registry.register(Kind::None, Box::new(InterpretNone), Level::L0);

        registry.register(
            Kind::PatternMatch,
            Box::new(InterpretPatternMatch {
                pattern_source: Box::new(crate::types::SlotType {
                    family: crate::types::Family::Top,
                    kind: crate::types::Kind::Top,
                    layer: crate::types::Layer::Top,
                    affinity: crate::types::Affinity::Top,
                    lower: 0,
                    upper: crate::types::UpperBound::Infinite,
                    id: crate::types::TypeId(0),
                    meta: crate::types::TypeMeta::None,
                }),
                pattern_target: Box::new(crate::types::SlotType {
                    family: crate::types::Family::Top,
                    kind: crate::types::Kind::Top,
                    layer: crate::types::Layer::Top,
                    affinity: crate::types::Affinity::Top,
                    lower: 0,
                    upper: crate::types::UpperBound::Infinite,
                    id: crate::types::TypeId(0),
                    meta: crate::types::TypeMeta::None,
                }),
                pos_predicate: Box::new(|_| false),
            }),
            Level::L0,
        );

        registry.register(
            Kind::Eq,
            Box::new(InterpretEq {
                i_eq: 0,
                id_pairs: std::collections::HashSet::new(),
            }),
            Level::L0,
        );

        registry
    }

    pub fn lookup(&self, kind: Kind) -> Option<(&dyn Interpretation, Level)> {
        let interpretation = self.interpretations.get(&kind)?;
        let level = self.levels.get(&kind)?;
        Some((interpretation.as_ref(), *level))
    }

    pub fn register(&mut self, kind: Kind, interpretation: Box<dyn Interpretation>, level: Level) {
        self.interpretations.insert(kind, interpretation);
        self.levels.insert(kind, level);
    }
}

impl Default for KindRegistry {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::admissibility::InterpretAny;
    use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};

    #[test]
    fn with_base_kinds_registers_all_base_kinds() {
        let registry = KindRegistry::with_base_kinds();

        assert!(registry.lookup(Kind::Any).is_some());
        assert!(registry.lookup(Kind::None).is_some());
        assert!(registry.lookup(Kind::PatternMatch).is_some());
        assert!(registry.lookup(Kind::Eq).is_some());
    }

    #[test]
    fn lookup_any_returns_interpret_any_and_l0() {
        let registry = KindRegistry::with_base_kinds();
        let result = registry.lookup(Kind::Any);

        assert!(result.is_some());
        let (interpretation, level) = result.unwrap();
        assert_eq!(level, Level::L0);

        assert!(interpretation.interpret(
            &SlotType {
                family: Family::Rule,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(1),
                meta: TypeMeta::None,
            },
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(2),
                meta: TypeMeta::None,
            },
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(3),
                meta: TypeMeta::None,
            },
            0,
        ));
    }

    #[test]
    fn lookup_none_returns_interpret_none_and_l0() {
        let registry = KindRegistry::with_base_kinds();
        let result = registry.lookup(Kind::None);

        assert!(result.is_some());
        let (interpretation, level) = result.unwrap();
        assert_eq!(level, Level::L0);

        assert!(!interpretation.interpret(
            &SlotType {
                family: Family::Rule,
                kind: Kind::None,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(1),
                meta: TypeMeta::None,
            },
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(2),
                meta: TypeMeta::None,
            },
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(3),
                meta: TypeMeta::None,
            },
            0,
        ));
    }

    #[test]
    fn lookup_unknown_kind_returns_none() {
        let registry = KindRegistry::new();
        assert!(registry.lookup(Kind::Top).is_none());
        assert!(registry.lookup(Kind::Bot).is_none());
    }

    #[test]
    fn can_register_custom_kind() {
        let mut registry = KindRegistry::new();
        registry.register(Kind::Top, Box::new(InterpretAny), Level::L1);

        let result = registry.lookup(Kind::Top);
        assert!(result.is_some());
        let (_, level) = result.unwrap();
        assert_eq!(level, Level::L1);
    }

    #[test]
    fn registered_kind_is_retrievable_via_lookup() {
        let mut registry = KindRegistry::new();
        let custom_interpretation = Box::new(InterpretAny);
        registry.register(Kind::Bot, custom_interpretation, Level::LN(3));

        let result = registry.lookup(Kind::Bot);
        assert!(result.is_some());
        let (interpretation, level) = result.unwrap();
        assert_eq!(level, Level::LN(3));

        assert!(interpretation.interpret(
            &SlotType {
                family: Family::Rule,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(1),
                meta: TypeMeta::None,
            },
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(2),
                meta: TypeMeta::None,
            },
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(3),
                meta: TypeMeta::None,
            },
            0,
        ));
    }
}

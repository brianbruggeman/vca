use crate::relation::{PosIndex, Relation};
use crate::slot::SlotId;
use crate::system::VCASystem;
use crate::types::{SlotType, TypeMeta};
use std::collections::HashSet;

/// Rule interpretation function: determines whether a relation is admitted.
pub trait Interpretation {
    fn interpret(
        &self,
        rule_type: &SlotType,
        t_src: &SlotType,
        t_tgt: &SlotType,
        pos: PosIndex,
    ) -> bool;
}

/// Admits all relations unconditionally.
pub struct InterpretAny;

impl Interpretation for InterpretAny {
    fn interpret(
        &self,
        _rule_type: &SlotType,
        _t_src: &SlotType,
        _t_tgt: &SlotType,
        _pos: PosIndex,
    ) -> bool {
        true
    }
}

/// Admits no relations.
pub struct InterpretNone;

impl Interpretation for InterpretNone {
    fn interpret(
        &self,
        _rule_type: &SlotType,
        _t_src: &SlotType,
        _t_tgt: &SlotType,
        _pos: PosIndex,
    ) -> bool {
        false
    }
}

/// Metadata extracted from a rule slot for interpretation.
pub struct RuleMetadata {
    pub pattern_source: SlotType,
    pub pattern_target: SlotType,
    pub pos_predicate: Box<dyn Fn(PosIndex) -> bool>,
}

/// Admits relations where source and target types match given patterns.
pub struct InterpretPatternMatch {
    pub pattern_source: Box<SlotType>,
    pub pattern_target: Box<SlotType>,
    pub pos_predicate: Box<dyn Fn(PosIndex) -> bool>,
}

impl Interpretation for InterpretPatternMatch {
    fn interpret(
        &self,
        _rule_type: &SlotType,
        t_src: &SlotType,
        t_tgt: &SlotType,
        pos: PosIndex,
    ) -> bool {
        use crate::types::slot_type_matches;
        slot_type_matches(&self.pattern_source, t_src)
            && slot_type_matches(&self.pattern_target, t_tgt)
            && (self.pos_predicate)(pos)
    }
}

/// Admits relations at a specific position where source/target id pairs match.
pub struct InterpretEq {
    pub i_eq: PosIndex,
    pub id_pairs: HashSet<(u64, u64)>,
}

impl Interpretation for InterpretEq {
    fn interpret(
        &self,
        _rule_type: &SlotType,
        _t_src: &SlotType,
        _t_tgt: &SlotType,
        pos: PosIndex,
    ) -> bool {
        if pos != self.i_eq {
            return false;
        }
        let id_src = _t_src.id.0;
        let id_tgt = _t_tgt.id.0;
        self.id_pairs.contains(&(id_src, id_tgt))
    }
}

/// Returns true if the given rule slot admits the relation.
pub fn admits(system: &VCASystem, rule: SlotId, relation: &Relation) -> bool {
    let Some(rule_type) = system.type_of(rule) else {
        return false;
    };
    if rule_type.family != crate::types::Family::Rule {
        return false;
    }

    let Some(t_src) = system.type_of(relation.source) else {
        return false;
    };
    let Some(t_tgt) = system.type_of(relation.target) else {
        return false;
    };

    let interpretation: Box<dyn Interpretation> = match rule_type.kind {
        crate::types::Kind::Any => Box::new(InterpretAny),
        crate::types::Kind::None => Box::new(InterpretNone),
        crate::types::Kind::PatternMatch => match &rule_type.meta {
            TypeMeta::PatternMatch {
                pattern_source,
                pattern_target,
            } => Box::new(InterpretPatternMatch {
                pattern_source: pattern_source.clone(),
                pattern_target: pattern_target.clone(),
                pos_predicate: Box::new(|_| true),
            }),
            _ => return false,
        },
        crate::types::Kind::Eq => match &rule_type.meta {
            TypeMeta::Eq { i_eq, id_pairs } => Box::new(InterpretEq {
                i_eq: *i_eq,
                id_pairs: id_pairs.clone(),
            }),
            _ => return false,
        },
        _ => Box::new(InterpretNone),
    };

    interpretation.interpret(rule_type, t_src, t_tgt, relation.position)
}

/// Returns true if any rule in the system admits the relation (Theorem 4).
pub fn is_admissible(system: &VCASystem, relation: &Relation) -> bool {
    let rule_slots = system.rule_slots();
    for rule in rule_slots {
        if admits(system, rule, relation) {
            return true;
        }
    }
    false
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};
    use std::collections::HashSet;

    #[test]
    fn interpret_any_returns_true_for_any_input() {
        let interp = InterpretAny;
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

        let test_cases = vec![
            (
                SlotType {
                    family: Family::Data,
                    kind: Kind::Any,
                    layer: Layer::N(0),
                    affinity: Affinity::Strict,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId(2),
                    meta: TypeMeta::None,
                },
                SlotType {
                    family: Family::Data,
                    kind: Kind::Any,
                    layer: Layer::N(0),
                    affinity: Affinity::Strict,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId(2),
                    meta: TypeMeta::None,
                },
                0,
            ),
            (
                SlotType {
                    family: Family::Rule,
                    kind: Kind::PatternMatch,
                    layer: Layer::N(999),
                    affinity: Affinity::Lax,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId(4),
                    meta: TypeMeta::None,
                },
                SlotType {
                    family: Family::Top,
                    kind: Kind::Bot,
                    layer: Layer::Top,
                    affinity: Affinity::Bot,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId(5),
                    meta: TypeMeta::None,
                },
                42,
            ),
        ];

        for (t_src, t_tgt, pos) in test_cases {
            assert!(interp.interpret(&rule_type, &t_src, &t_tgt, pos));
        }
    }

    #[test]
    fn interpret_none_returns_false_for_any_input() {
        let interp = InterpretNone;
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

        let test_cases = vec![
            (
                SlotType {
                    family: Family::Data,
                    kind: Kind::Any,
                    layer: Layer::N(0),
                    affinity: Affinity::Strict,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId(2),
                    meta: TypeMeta::None,
                },
                SlotType {
                    family: Family::Data,
                    kind: Kind::Any,
                    layer: Layer::N(0),
                    affinity: Affinity::Strict,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId(2),
                    meta: TypeMeta::None,
                },
                0,
            ),
            (
                SlotType {
                    family: Family::Rule,
                    kind: Kind::PatternMatch,
                    layer: Layer::N(999),
                    affinity: Affinity::Lax,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId(4),
                    meta: TypeMeta::None,
                },
                SlotType {
                    family: Family::Top,
                    kind: Kind::Bot,
                    layer: Layer::Top,
                    affinity: Affinity::Bot,
                    lower: 0,
                    upper: UpperBound::Infinite,
                    id: TypeId(5),
                    meta: TypeMeta::None,
                },
                42,
            ),
        ];

        for (t_src, t_tgt, pos) in test_cases {
            assert!(!interp.interpret(&rule_type, &t_src, &t_tgt, pos,));
        }
    }

    #[test]
    fn interpret_pattern_match_matches_correctly() {
        let interp = InterpretPatternMatch {
            pattern_source: Box::new(SlotType {
                family: Family::Top,
                kind: Kind::Top,
                layer: Layer::Top,
                affinity: Affinity::Top,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(10),
                meta: TypeMeta::None,
            }),
            pattern_target: Box::new(SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(11),
                meta: TypeMeta::None,
            }),
            pos_predicate: Box::new(|p| p == 0),
        };

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::PatternMatch,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };

        let t_src = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Lax,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let t_tgt = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(3),
            meta: TypeMeta::None,
        };

        assert!(interp.interpret(&rule_type, &t_src, &t_tgt, 0,));

        assert!(!interp.interpret(&rule_type, &t_src, &t_tgt, 1,));
    }

    #[test]
    fn interpret_pattern_match_fails_on_source_type_mismatch() {
        let interp = InterpretPatternMatch {
            pattern_source: Box::new(SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(10),
                meta: TypeMeta::None,
            }),
            pattern_target: Box::new(SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(11),
                meta: TypeMeta::None,
            }),
            pos_predicate: Box::new(|_| true),
        };

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::PatternMatch,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };

        let t_src = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let t_tgt = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(3),
            meta: TypeMeta::None,
        };

        assert!(!interp.interpret(&rule_type, &t_src, &t_tgt, 0,));
    }

    #[test]
    fn interpret_pattern_match_fails_on_target_type_mismatch() {
        let interp = InterpretPatternMatch {
            pattern_source: Box::new(SlotType {
                family: Family::Top,
                kind: Kind::Top,
                layer: Layer::Top,
                affinity: Affinity::Top,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(10),
                meta: TypeMeta::None,
            }),
            pattern_target: Box::new(SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(11),
                meta: TypeMeta::None,
            }),
            pos_predicate: Box::new(|_| true),
        };

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::PatternMatch,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };

        let t_src = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Lax,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let t_tgt = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(3),
            meta: TypeMeta::None,
        };

        assert!(!interp.interpret(&rule_type, &t_src, &t_tgt, 0,));
    }

    #[test]
    fn interpret_pattern_match_fails_on_position_predicate() {
        let interp = InterpretPatternMatch {
            pattern_source: Box::new(SlotType {
                family: Family::Top,
                kind: Kind::Top,
                layer: Layer::Top,
                affinity: Affinity::Top,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(10),
                meta: TypeMeta::None,
            }),
            pattern_target: Box::new(SlotType {
                family: Family::Top,
                kind: Kind::Top,
                layer: Layer::Top,
                affinity: Affinity::Top,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(11),
                meta: TypeMeta::None,
            }),
            pos_predicate: Box::new(|p| p == 0),
        };

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::PatternMatch,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };

        let t_src = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Lax,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let t_tgt = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(3),
            meta: TypeMeta::None,
        };

        assert!(interp.interpret(&rule_type, &t_src, &t_tgt, 0,));

        assert!(!interp.interpret(&rule_type, &t_src, &t_tgt, 1,));
    }

    #[test]
    fn interpret_eq_matches_correctly() {
        let mut id_pairs = HashSet::new();
        id_pairs.insert((1, 2));
        id_pairs.insert((3, 4));

        let interp = InterpretEq { i_eq: 0, id_pairs };

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Eq,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };

        assert!(interp.interpret(
            &rule_type,
            &SlotType {
                family: Family::Data,
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
            0,
        ));

        assert!(!interp.interpret(
            &rule_type,
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
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(4),
                meta: TypeMeta::None,
            },
            1,
        ));

        assert!(!interp.interpret(
            &rule_type,
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(4),
                meta: TypeMeta::None,
            },
            &SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(5),
                meta: TypeMeta::None,
            },
            0,
        ));
    }

    fn make_system_with_rule(kind: Kind) -> VCASystem {
        let rule_slot = SlotId(1);
        let data_slot = SlotId(2);

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

        let mut system = VCASystem::new(rule_slot, rule_type.clone()).unwrap();

        system.slots.push(data_slot);
        system.types.insert(data_slot, data_type);

        system
    }

    #[test]
    fn is_admissible_with_any_kind() {
        let system = make_system_with_rule(Kind::Any);
        let relation = Relation {
            source: SlotId(2),
            target: SlotId(2),
            position: 0,
        };

        assert!(is_admissible(&system, &relation));
    }

    #[test]
    fn is_admissible_with_none_kind() {
        let system = make_system_with_rule(Kind::None);
        let relation = Relation {
            source: SlotId(2),
            target: SlotId(2),
            position: 0,
        };

        assert!(!is_admissible(&system, &relation));
    }

    #[test]
    fn is_admissible_with_multiple_rules_any_admits() {
        let rule1 = SlotId(1);
        let rule2 = SlotId(2);
        let data = SlotId(3);

        let rule_type_any = SlotType {
            family: Family::Rule,
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
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let data_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(3),
            meta: TypeMeta::None,
        };

        let mut system = VCASystem::new(rule1, rule_type_any.clone()).unwrap();

        system.slots.push(rule2);
        system.slots.push(data);
        system.types.insert(rule2, rule_type_none);
        system.types.insert(data, data_type);

        let relation = Relation {
            source: data,
            target: data,
            position: 0,
        };

        assert!(is_admissible(&system, &relation));
    }

    #[test]
    fn is_admissible_with_only_none_rules() {
        let rule1 = SlotId(1);
        let rule2 = SlotId(2);
        let data = SlotId(3);

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

        let mut system = VCASystem::new(rule1, rule_type_none.clone()).unwrap();

        system.slots.push(rule2);
        system.slots.push(data);
        system.types.insert(rule2, rule_type_none);
        system.types.insert(data, data_type);

        let relation = Relation {
            source: data,
            target: data,
            position: 0,
        };

        assert!(!is_admissible(&system, &relation));
    }

    #[test]
    fn admits_pattern_match_via_typemeta() {
        let rule_slot = SlotId(1);
        let data1 = SlotId(2);
        let data2 = SlotId(3);

        let pattern_source = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(0),
            meta: TypeMeta::None,
        };
        let pattern_target = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(0),
            meta: TypeMeta::None,
        };

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::PatternMatch,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::PatternMatch {
                pattern_source: Box::new(pattern_source),
                pattern_target: Box::new(pattern_target),
            },
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

        let mut system = VCASystem::new(rule_slot, rule_type.clone()).unwrap();
        system.slots.push(data1);
        system.slots.push(data2);
        system.types.insert(data1, data_type.clone());
        system.types.insert(data2, data_type);

        let matching_relation = Relation {
            source: data1,
            target: data2,
            position: 0,
        };

        assert!(is_admissible(&system, &matching_relation));
    }

    #[test]
    fn admits_eq_via_typemeta() {
        let rule_slot = SlotId(1);
        let data1 = SlotId(2);
        let data2 = SlotId(3);

        let mut id_pairs = HashSet::new();
        id_pairs.insert((2, 2));

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Eq,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::Eq { i_eq: 0, id_pairs },
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

        let mut system = VCASystem::new(rule_slot, rule_type.clone()).unwrap();
        system.slots.push(data1);
        system.slots.push(data2);
        system.types.insert(data1, data_type.clone());
        system.types.insert(data2, data_type);

        let matching_relation = Relation {
            source: data1,
            target: data2,
            position: 0,
        };

        assert!(is_admissible(&system, &matching_relation));

        let non_matching_relation = Relation {
            source: data1,
            target: data2,
            position: 1,
        };

        assert!(!is_admissible(&system, &non_matching_relation));
    }

    #[test]
    fn admits_pattern_match_graceful_failure() {
        let rule_slot = SlotId(1);
        let data1 = SlotId(2);
        let data2 = SlotId(3);

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::PatternMatch,
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

        let mut system = VCASystem::new(rule_slot, rule_type.clone()).unwrap();
        system.slots.push(data1);
        system.slots.push(data2);
        system.types.insert(data1, data_type.clone());
        system.types.insert(data2, data_type);

        let relation = Relation {
            source: data1,
            target: data2,
            position: 0,
        };

        assert!(!is_admissible(&system, &relation));
    }

    #[test]
    fn admits_eq_graceful_failure() {
        let rule_slot = SlotId(1);
        let data1 = SlotId(2);
        let data2 = SlotId(3);

        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Eq,
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

        let mut system = VCASystem::new(rule_slot, rule_type.clone()).unwrap();
        system.slots.push(data1);
        system.slots.push(data2);
        system.types.insert(data1, data_type.clone());
        system.types.insert(data2, data_type);

        let relation = Relation {
            source: data1,
            target: data2,
            position: 0,
        };

        assert!(!is_admissible(&system, &relation));
    }
}

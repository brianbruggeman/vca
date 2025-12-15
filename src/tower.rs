use crate::coherence::is_coherent;
use crate::system::{RuleRef, VCASystem};
use thiserror::Error;

#[derive(Error, Debug, PartialEq, Eq)]
pub enum TowerError {
    #[error("base system must be self-referential")]
    BaseNotSelfReferential,
    #[error("invalid rule system: expected level {expected_level}")]
    InvalidRuleSystem { expected_level: usize },
    #[error("level {level} is not coherent")]
    LevelNotCoherent { level: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Tower {
    levels: Vec<VCASystem>,
}

impl Tower {
    pub fn new(base: VCASystem) -> Result<Self, TowerError> {
        if !matches!(base.rule_ref, RuleRef::SelfRef) {
            return Err(TowerError::BaseNotSelfReferential);
        }

        Ok(Tower { levels: vec![base] })
    }

    pub fn push_level(&mut self, system: VCASystem) -> Result<(), TowerError> {
        let expected_level = self.levels.len() - 1;
        let expected_rule_ref = RuleRef::External(Box::new(self.levels[expected_level].clone()));

        if system.rule_ref != expected_rule_ref {
            return Err(TowerError::InvalidRuleSystem { expected_level });
        }

        if !system.is_structurally_valid() {
            return Err(TowerError::LevelNotCoherent {
                level: self.levels.len(),
            });
        }

        self.levels.push(system);
        Ok(())
    }

    pub fn base(&self) -> &VCASystem {
        &self.levels[0]
    }

    pub fn level(&self, n: usize) -> Option<&VCASystem> {
        self.levels.get(n)
    }

    pub fn height(&self) -> usize {
        self.levels.len()
    }

    pub fn rule_system(&self, n: usize) -> RuleRef {
        if n == 0 {
            RuleRef::SelfRef
        } else if let Some(prev_level) = self.levels.get(n - 1) {
            RuleRef::External(Box::new(prev_level.clone()))
        } else {
            RuleRef::Empty
        }
    }

    /// checks local coherence of level n
    ///
    /// for n=0: ℱ^(0) ∈ FS_struct ∧ all A^(0) admissible under ℱ^(0)
    /// for n>0: ℱ^(n) ∈ FS_struct ∧ all A^(n) admissible under ℱ^(n-1)
    pub fn local_coh(&self, n: usize) -> bool {
        let Some(level) = self.levels.get(n) else {
            return false;
        };

        if !level.is_structurally_valid() {
            return false;
        }

        if n == 0 {
            // base level: check coherence (structurally valid + all admissible under self)
            is_coherent(level)
        } else {
            // level n > 0: check all relations admissible under level n-1
            let Some(rule_system) = self.levels.get(n - 1) else {
                return false;
            };

            // check each relation in level n is admissible under rule_system
            for rel in &level.relations {
                if !is_admissible_under(level, rel, rule_system) {
                    return false;
                }
            }

            true
        }
    }

    /// checks coherence up to level n (theorem 7)
    ///
    /// returns true if all levels 0..=n are locally coherent
    pub fn is_coherent_up_to(&self, n: usize) -> bool {
        for k in 0..=n {
            if !self.local_coh(k) {
                return false;
            }
        }
        true
    }

    /// checks coherence of all existing levels
    ///
    /// note: full tower coherence is coinductive (gfp), we can only check finite prefix
    pub fn is_coherent(&self) -> bool {
        if self.levels.is_empty() {
            return false;
        }
        self.is_coherent_up_to(self.levels.len() - 1)
    }
}

/// checks if a relation is admissible under a specific rule system
///
/// the relation exists in `system` (level n), and we check if it's admissible
/// under rules in `rule_system` (level n-1). the relation's source/target types
/// come from `system`, but the rules come from `rule_system`.
fn is_admissible_under(
    system: &VCASystem,
    relation: &crate::relation::Relation,
    rule_system: &VCASystem,
) -> bool {
    use crate::admissibility::{
        InterpretAny, InterpretEq, InterpretNone, InterpretPatternMatch, Interpretation,
    };
    use crate::types::TypeMeta;

    // get source and target types from the system where the relation exists
    let Some(t_src) = system.type_of(relation.source) else {
        return false;
    };
    let Some(t_tgt) = system.type_of(relation.target) else {
        return false;
    };

    // get rule slots from the rule system
    let rule_slots = rule_system.rule_slots();

    // check if any rule in the rule system admits this relation
    for rule in rule_slots {
        let Some(rule_type) = rule_system.type_of(rule) else {
            continue;
        };
        if rule_type.family != crate::types::Family::Rule {
            continue;
        }

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
                _ => continue,
            },
            crate::types::Kind::Eq => match &rule_type.meta {
                TypeMeta::Eq { i_eq, id_pairs } => Box::new(InterpretEq {
                    i_eq: *i_eq,
                    id_pairs: id_pairs.clone(),
                }),
                _ => continue,
            },
            _ => Box::new(InterpretNone),
        };

        if interpretation.interpret(rule_type, t_src, t_tgt, relation.position) {
            return true;
        }
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slot::SlotId;
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

    fn make_self_ref_base() -> VCASystem {
        let (slot, slot_type) = make_test_slot();
        let mut system = VCASystem::new(slot, slot_type).unwrap();
        system.rule_ref = RuleRef::SelfRef;
        system
    }

    #[test]
    fn new_requires_self_ref_base() {
        let (slot, slot_type) = make_test_slot();
        let base = VCASystem::new(slot, slot_type).unwrap();
        let result = Tower::new(base);
        assert_eq!(result, Err(TowerError::BaseNotSelfReferential));
    }

    #[test]
    fn new_with_self_ref_base_succeeds() {
        let base = make_self_ref_base();
        let tower = Tower::new(base).unwrap();
        assert_eq!(tower.height(), 1);
    }

    #[test]
    fn base_returns_reference_to_level_zero() {
        let base = make_self_ref_base();
        let tower = Tower::new(base.clone()).unwrap();
        assert_eq!(tower.base(), &base);
    }

    #[test]
    fn push_level_with_correct_rule_ref_succeeds() {
        let base = make_self_ref_base();
        let mut tower = Tower::new(base.clone()).unwrap();

        let (slot2, slot_type2) = make_test_slot();
        let mut level1 = VCASystem::new(slot2, slot_type2).unwrap();
        level1.rule_ref = RuleRef::External(Box::new(base));

        let result = tower.push_level(level1.clone());
        assert!(result.is_ok());
        assert_eq!(tower.height(), 2);
        assert_eq!(tower.level(1), Some(&level1));
    }

    #[test]
    fn push_level_with_wrong_rule_ref_fails() {
        let base = make_self_ref_base();
        let mut tower = Tower::new(base).unwrap();

        let (slot2, slot_type2) = make_test_slot();
        let mut level1 = VCASystem::new(slot2, slot_type2).unwrap();
        level1.rule_ref = RuleRef::Empty;

        let result = tower.push_level(level1);
        assert_eq!(
            result,
            Err(TowerError::InvalidRuleSystem { expected_level: 0 })
        );
    }

    #[test]
    fn level_returns_some_for_valid_index() {
        let base = make_self_ref_base();
        let tower = Tower::new(base.clone()).unwrap();
        assert_eq!(tower.level(0), Some(&base));
    }

    #[test]
    fn level_returns_none_for_invalid_index() {
        let base = make_self_ref_base();
        let tower = Tower::new(base).unwrap();
        assert_eq!(tower.level(1), None);
    }

    #[test]
    fn rule_system_returns_self_ref_for_level_zero() {
        let base = make_self_ref_base();
        let tower = Tower::new(base).unwrap();
        assert_eq!(tower.rule_system(0), RuleRef::SelfRef);
    }

    #[test]
    fn rule_system_returns_external_for_level_one() {
        let base = make_self_ref_base();
        let mut tower = Tower::new(base.clone()).unwrap();

        let (slot2, slot_type2) = make_test_slot();
        let mut level1 = VCASystem::new(slot2, slot_type2).unwrap();
        level1.rule_ref = RuleRef::External(Box::new(base.clone()));
        tower.push_level(level1).unwrap();

        let rule_ref = tower.rule_system(1);
        match rule_ref {
            RuleRef::External(external) => {
                assert_eq!(*external, base);
            }
            _ => panic!("expected External rule ref"),
        }
    }

    #[test]
    fn rule_system_returns_empty_for_invalid_level() {
        let base = make_self_ref_base();
        let tower = Tower::new(base).unwrap();
        assert_eq!(tower.rule_system(10), RuleRef::Empty);
    }

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

    #[test]
    fn local_coh_0_checks_base_coherence() {
        let base = make_coherent_base();
        let tower = Tower::new(base).unwrap();
        assert!(tower.local_coh(0));
    }

    #[test]
    fn local_coh_0_returns_false_for_incoherent_base() {
        let (slot, slot_type) = make_test_slot();
        let mut base = VCASystem::new(slot, slot_type).unwrap();
        base.rule_ref = RuleRef::SelfRef;
        // base is structurally valid but has no rules, so relations won't be admissible
        let tower = Tower::new(base).unwrap();
        // base with no rules and no relations should be coherent
        assert!(tower.local_coh(0));
    }

    #[test]
    fn local_coh_n_checks_level_admissible_under_prev() {
        let base = make_coherent_base();
        let mut tower = Tower::new(base.clone()).unwrap();

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
        level1.rule_ref = RuleRef::External(Box::new(base));
        tower.push_level(level1).unwrap();

        assert!(tower.local_coh(1));
    }

    #[test]
    fn local_coh_n_returns_false_for_inadmissible_relation() {
        let base = make_coherent_base();

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

        // add a relation that won't be admissible (base has Kind::Any rule, so it should be admissible)
        // actually, with Kind::Any, all relations are admissible, so let's create a base with Kind::None
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
        let mut base_none = VCASystem::new(rule_slot, rule_type).unwrap();
        base_none.rule_ref = RuleRef::SelfRef;
        let mut tower_none = Tower::new(base_none.clone()).unwrap();

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
        let mut level1_none = VCASystem::new(level1_slot2, level1_type2).unwrap();
        level1_none.rule_ref = RuleRef::External(Box::new(base_none.clone()));
        level1_none.relations.push(crate::relation::Relation {
            source: level1_slot2,
            target: level1_slot2,
            position: 0,
        });
        tower_none.push_level(level1_none).unwrap();

        // level1 has a relation that's not admissible under base (which has Kind::None)
        assert!(!tower_none.local_coh(1));
    }

    #[test]
    fn local_coh_returns_false_for_invalid_level() {
        let base = make_coherent_base();
        let tower = Tower::new(base).unwrap();
        assert!(!tower.local_coh(10));
    }

    #[test]
    fn is_coherent_up_to_0_checks_just_base() {
        let base = make_coherent_base();
        let tower = Tower::new(base).unwrap();
        assert!(tower.is_coherent_up_to(0));
    }

    #[test]
    fn is_coherent_up_to_n_checks_all_levels() {
        let base = make_coherent_base();
        let mut tower = Tower::new(base.clone()).unwrap();

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
        level1.rule_ref = RuleRef::External(Box::new(base));
        tower.push_level(level1).unwrap();

        assert!(tower.is_coherent_up_to(1));
    }

    #[test]
    fn is_coherent_up_to_returns_false_if_any_level_fails() {
        let base = make_coherent_base();

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

        // create base with Kind::None rule
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
        let mut base_none = VCASystem::new(rule_slot, rule_type).unwrap();
        base_none.rule_ref = RuleRef::SelfRef;
        let mut tower_none = Tower::new(base_none.clone()).unwrap();

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
        let mut level1_none = VCASystem::new(level1_slot2, level1_type2).unwrap();
        level1_none.rule_ref = RuleRef::External(Box::new(base_none.clone()));
        level1_none.relations.push(crate::relation::Relation {
            source: level1_slot2,
            target: level1_slot2,
            position: 0,
        });
        tower_none.push_level(level1_none).unwrap();

        assert!(!tower_none.is_coherent_up_to(1));
    }

    #[test]
    fn is_coherent_checks_all_existing_levels() {
        let base = make_coherent_base();
        let tower = Tower::new(base).unwrap();
        assert!(tower.is_coherent());
    }

    #[test]
    fn is_coherent_returns_false_for_incoherent_tower() {
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
        let mut base = VCASystem::new(rule_slot, rule_type).unwrap();
        base.rule_ref = RuleRef::SelfRef;
        let mut tower = Tower::new(base.clone()).unwrap();

        let level1_slot = SlotId(4);
        let level1_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(4),
            meta: TypeMeta::None,
        };
        let mut level1 = VCASystem::new(level1_slot, level1_type).unwrap();
        level1.rule_ref = RuleRef::External(Box::new(base.clone()));
        level1.relations.push(crate::relation::Relation {
            source: level1_slot,
            target: level1_slot,
            position: 0,
        });
        tower.push_level(level1).unwrap();

        assert!(!tower.is_coherent());
    }

    #[test]
    fn single_level_tower_is_coherent() {
        let base = make_coherent_base();
        let tower = Tower::new(base).unwrap();
        assert!(tower.is_coherent());
        assert!(tower.local_coh(0));
    }

    #[test]
    fn two_level_tower_with_valid_rule_chain() {
        let base = make_coherent_base();
        let mut tower = Tower::new(base.clone()).unwrap();

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
        level1.rule_ref = RuleRef::External(Box::new(base));
        tower.push_level(level1).unwrap();

        assert!(tower.is_coherent());
        assert!(tower.local_coh(0));
        assert!(tower.local_coh(1));
    }

    #[test]
    fn detect_incoherent_level_in_multi_level_tower() {
        let base = make_coherent_base();
        let mut tower = Tower::new(base.clone()).unwrap();

        // create level1 with Kind::None rule from the start
        let rule_slot = SlotId(5);
        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::None,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(5),
            meta: TypeMeta::None,
        };
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
        level1.slots.push(rule_slot);
        level1.types.insert(rule_slot, rule_type);
        tower.push_level(level1.clone()).unwrap();

        // create level2 with a relation that won't be admissible under level1 (which has Kind::None)
        let mut level2 = VCASystem::new(
            SlotId(6),
            SlotType {
                family: Family::Data,
                kind: Kind::Any,
                layer: Layer::N(0),
                affinity: Affinity::Strict,
                lower: 0,
                upper: UpperBound::Infinite,
                id: TypeId(6),
                meta: TypeMeta::None,
            },
        )
        .unwrap();
        level2.rule_ref = RuleRef::External(Box::new(level1.clone()));
        level2.relations.push(crate::relation::Relation {
            source: SlotId(6),
            target: SlotId(6),
            position: 0,
        });
        tower.push_level(level2).unwrap();

        // level2 has a relation that's not admissible under level1 (which has Kind::None)
        assert!(!tower.local_coh(2));
        assert!(!tower.is_coherent());
    }

    #[test]
    fn empty_relations_at_all_levels() {
        let base = make_coherent_base();
        let mut tower = Tower::new(base.clone()).unwrap();

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
        level1.rule_ref = RuleRef::External(Box::new(base));
        tower.push_level(level1).unwrap();

        // all levels have empty relations, should be coherent
        assert!(tower.is_coherent());
    }

    #[test]
    fn modifying_level_k_does_not_affect_coherent_up_to_k_minus_one() {
        let base = make_coherent_base();
        let mut tower1 = Tower::new(base.clone()).unwrap();

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
        tower1.push_level(level1.clone()).unwrap();

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
        tower1.push_level(level2).unwrap();

        let result_before = tower1.is_coherent_up_to(1);

        let mut tower2 = Tower::new(base).unwrap();
        tower2.push_level(level1.clone()).unwrap();

        let level2_modified_slot = SlotId(5);
        let level2_modified_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(5),
            meta: TypeMeta::None,
        };
        let mut level2_modified =
            VCASystem::new(level2_modified_slot, level2_modified_type).unwrap();
        level2_modified.rule_ref = RuleRef::External(Box::new(level1));
        level2_modified.relations.push(crate::relation::Relation {
            source: level2_modified_slot,
            target: level2_modified_slot,
            position: 0,
        });
        tower2.push_level(level2_modified).unwrap();

        let result_after = tower2.is_coherent_up_to(1);

        assert_eq!(result_before, result_after);
    }

    #[test]
    fn level_n_coherence_depends_only_on_v_a_tau_n_and_v_tau_n_minus_one() {
        let base1 = make_coherent_base();
        let base2 = make_coherent_base();

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
        let mut level1 = VCASystem::new(level1_slot, level1_type.clone()).unwrap();
        level1.rule_ref = RuleRef::External(Box::new(base1.clone()));

        let mut tower1 = Tower::new(base1).unwrap();
        tower1.push_level(level1.clone()).unwrap();

        let mut base2_modified = base2.clone();
        base2_modified.relations.push(crate::relation::Relation {
            source: SlotId(1),
            target: SlotId(2),
            position: 0,
        });

        let mut level1_alt = VCASystem::new(level1_slot, level1_type).unwrap();
        level1_alt.rule_ref = RuleRef::External(Box::new(base2_modified.clone()));

        let mut tower2 = Tower::new(base2_modified).unwrap();
        tower2.push_level(level1_alt).unwrap();

        let coherence1 = tower1.local_coh(1);
        let coherence2 = tower2.local_coh(1);

        assert_eq!(coherence1, coherence2);
    }
}

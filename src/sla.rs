use std::cmp::Ordering;

use crate::coherence::is_coherent;
use crate::relation::PosIndex;
use crate::slot::SlotId;
use crate::system::VCASystem;
use crate::temporal::TemporalFormula;
use crate::tower::Tower;
use crate::types::SlotType;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StatePredicate {
    Coherent,
    SlotExists(SlotId),
    RelationExists(SlotId, SlotId, PosIndex),
    TypeMatches(SlotId, SlotType),
    SlotCount(Ordering, usize),
}

pub type SLA = TemporalFormula<StatePredicate>;

fn eval_predicate(system: &VCASystem, predicate: &StatePredicate) -> bool {
    match predicate {
        StatePredicate::Coherent => is_coherent(system),
        StatePredicate::SlotExists(id) => system.contains_slot(*id),
        StatePredicate::RelationExists(u, v, i) => system
            .relations
            .iter()
            .any(|rel| rel.source == *u && rel.target == *v && rel.position == *i),
        StatePredicate::TypeMatches(id, expected_type) => system
            .type_of(*id)
            .map(|actual_type| actual_type == expected_type)
            .unwrap_or(false),
        StatePredicate::SlotCount(ordering, count) => {
            let actual_count = system.slot_count();
            match ordering {
                Ordering::Less => actual_count < *count,
                Ordering::Equal => actual_count == *count,
                Ordering::Greater => actual_count > *count,
            }
        }
    }
}

pub fn check_sla(sla: &SLA, tower: &Tower, up_to: usize) -> bool {
    if tower.height() == 0 {
        return false;
    }

    let max_level = (tower.height() - 1).min(up_to);

    let trace: Vec<VCASystem> = (0..=max_level)
        .filter_map(|i| tower.level(i))
        .cloned()
        .collect();

    if trace.is_empty() {
        return false;
    }

    sla.check_up_to(&trace, eval_predicate, trace.len())
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::relation::Relation;
    use crate::system::RuleRef;
    use crate::types::{Affinity, Family, Kind, Layer, TypeId, TypeMeta, UpperBound};

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

    fn make_coherent_system() -> VCASystem {
        let slot_id = SlotId(1);
        let slot_type = make_test_slot_type();
        let mut system = VCASystem::new(slot_id, slot_type).expect("test system should be valid");
        system.rule_ref = RuleRef::SelfRef;
        system
    }

    #[test]
    fn coherent_predicate_checks_is_coherent() {
        let system = make_coherent_system();
        let predicate = StatePredicate::Coherent;
        assert!(eval_predicate(&system, &predicate));
    }

    #[test]
    fn slot_exists_predicate_checks_contains_slot() {
        let system = make_coherent_system();
        let predicate = StatePredicate::SlotExists(SlotId(1));
        assert!(eval_predicate(&system, &predicate));

        let predicate = StatePredicate::SlotExists(SlotId(999));
        assert!(!eval_predicate(&system, &predicate));
    }

    #[test]
    fn relation_exists_predicate_checks_relation_in_a() {
        let mut system = make_coherent_system();
        let rel = Relation {
            source: SlotId(1),
            target: SlotId(1),
            position: 0,
        };
        system.relations.push(rel);

        let predicate = StatePredicate::RelationExists(SlotId(1), SlotId(1), 0);
        assert!(eval_predicate(&system, &predicate));

        let predicate = StatePredicate::RelationExists(SlotId(1), SlotId(1), 1);
        assert!(!eval_predicate(&system, &predicate));
    }

    #[test]
    fn type_matches_predicate_checks_type_equality() {
        let system = make_coherent_system();
        let expected_type = make_test_slot_type();
        let predicate = StatePredicate::TypeMatches(SlotId(1), expected_type.clone());
        assert!(eval_predicate(&system, &predicate));

        let mut different_type = expected_type;
        different_type.id = TypeId(999);
        let predicate = StatePredicate::TypeMatches(SlotId(1), different_type);
        assert!(!eval_predicate(&system, &predicate));

        let predicate = StatePredicate::TypeMatches(SlotId(999), make_test_slot_type());
        assert!(!eval_predicate(&system, &predicate));
    }

    #[test]
    fn slot_count_predicate_checks_slot_count() {
        let system = make_coherent_system();
        let predicate = StatePredicate::SlotCount(Ordering::Equal, 1);
        assert!(eval_predicate(&system, &predicate));

        let predicate = StatePredicate::SlotCount(Ordering::Less, 100);
        assert!(eval_predicate(&system, &predicate));

        let predicate = StatePredicate::SlotCount(Ordering::Greater, 0);
        assert!(eval_predicate(&system, &predicate));

        let predicate = StatePredicate::SlotCount(Ordering::Equal, 2);
        assert!(!eval_predicate(&system, &predicate));
    }

    #[test]
    fn sla_is_alias_for_temporal_formula_state_predicate() {
        let _sla: SLA = TemporalFormula::Prop(StatePredicate::Coherent);
    }

    #[test]
    fn can_construct_always_coherent() {
        let _sla: SLA = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));
    }

    #[test]
    fn check_sla_always_coherent_returns_true_when_all_levels_coherent() {
        let base = make_coherent_system();
        let tower = Tower::new(base).expect("tower should be valid");
        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::Coherent));
        assert!(check_sla(&sla, &tower, 0));
    }

    #[test]
    fn check_sla_eventually_slot_exists_returns_true_when_slot_exists_at_some_level() {
        let base = make_coherent_system();
        let tower = Tower::new(base).expect("tower should be valid");
        let sla = TemporalFormula::eventually(TemporalFormula::Prop(StatePredicate::SlotExists(
            SlotId(1),
        )));
        assert!(check_sla(&sla, &tower, 0));
    }

    #[test]
    fn check_sla_always_slot_count_returns_true_when_all_levels_satisfy() {
        let base = make_coherent_system();
        let tower = Tower::new(base).expect("tower should be valid");
        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::SlotCount(
            Ordering::Less,
            100,
        )));
        assert!(check_sla(&sla, &tower, 0));
    }

    #[test]
    fn check_sla_always_slot_count_returns_false_when_one_level_violates() {
        let base = make_coherent_system();
        let tower = Tower::new(base).expect("tower should be valid");
        let sla = TemporalFormula::always(TemporalFormula::Prop(StatePredicate::SlotCount(
            Ordering::Less,
            1,
        )));
        assert!(!check_sla(&sla, &tower, 0));
    }
}

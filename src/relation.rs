use crate::slot::SlotId;

pub type PosIndex = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Relation {
    pub source: SlotId,
    pub target: SlotId,
    pub position: PosIndex,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[rstest::rstest]
    #[case::same_all_fields(
        Relation { source: SlotId(1), target: SlotId(2), position: 0 },
        Relation { source: SlotId(1), target: SlotId(2), position: 0 },
        true
    )]
    #[case::different_source(
        Relation { source: SlotId(1), target: SlotId(2), position: 0 },
        Relation { source: SlotId(3), target: SlotId(2), position: 0 },
        false
    )]
    #[case::different_target(
        Relation { source: SlotId(1), target: SlotId(2), position: 0 },
        Relation { source: SlotId(1), target: SlotId(3), position: 0 },
        false
    )]
    #[case::different_position(
        Relation { source: SlotId(1), target: SlotId(2), position: 0 },
        Relation { source: SlotId(1), target: SlotId(2), position: 1 },
        false
    )]
    fn relation_equality(#[case] a: Relation, #[case] b: Relation, #[case] expected: bool) {
        assert_eq!(a == b, expected);
    }
}

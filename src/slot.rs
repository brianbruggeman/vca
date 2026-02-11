/// Unique identifier for a slot in the system.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SlotId(pub u64);

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;

    #[rstest::rstest]
    #[case::same_values(SlotId(1), SlotId(1), true)]
    #[case::different_values(SlotId(1), SlotId(2), false)]
    fn slot_id_equality(#[case] a: SlotId, #[case] b: SlotId, #[case] expected: bool) {
        assert_eq!(a == b, expected);
    }

    #[test]
    fn slot_id_hashmap_key() {
        let mut map = HashMap::new();
        map.insert(SlotId(1), "first");
        map.insert(SlotId(2), "second");

        assert_eq!(map.get(&SlotId(1)), Some(&"first"));
        assert_eq!(map.get(&SlotId(2)), Some(&"second"));
        assert_eq!(map.get(&SlotId(3)), None);
    }
}

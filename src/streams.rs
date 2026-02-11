use crate::system::VCASystem;
use crate::transitions::{Transition, TransitionError};

/// An ordered sequence of transitions applied as a unit.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeltaStream(pub Vec<Transition>);

#[derive(Debug, PartialEq, Eq)]
pub enum StreamError {
    TransitionFailed {
        index: usize,
        error: TransitionError,
    },
}

impl std::fmt::Display for StreamError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TransitionFailed { index, error } => {
                write!(f, "transition at index {index} failed: {error:?}")
            }
        }
    }
}

impl std::error::Error for StreamError {}

impl DeltaStream {
    pub fn empty() -> Self {
        DeltaStream(Vec::new())
    }

    pub fn singleton(t: Transition) -> Self {
        DeltaStream(vec![t])
    }

    pub fn append(&mut self, t: Transition) {
        self.0.push(t);
    }

    pub fn concat(self, other: DeltaStream) -> Self {
        let mut combined = self.0;
        combined.extend(other.0);
        DeltaStream(combined)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

/// Applies all transitions in a stream sequentially, failing on first error.
pub fn apply_stream(stream: &DeltaStream, initial: &VCASystem) -> Result<VCASystem, StreamError> {
    let mut current = initial.clone();
    for (index, transition) in stream.0.iter().enumerate() {
        current = transition
            .apply(&current)
            .map_err(|error| StreamError::TransitionFailed { index, error })?;
    }
    Ok(current)
}

/// Applies a stream with a callback invoked before each transition.
pub fn apply_stream_with_callback<F>(
    stream: &DeltaStream,
    initial: &VCASystem,
    mut on_transition: F,
) -> Result<VCASystem, StreamError>
where
    F: FnMut(usize, &Transition, &VCASystem) -> Result<(), StreamError>,
{
    let mut current = initial.clone();
    for (index, transition) in stream.0.iter().enumerate() {
        on_transition(index, transition, &current)?;
        current = transition
            .apply(&current)
            .map_err(|error| StreamError::TransitionFailed { index, error })?;
    }
    Ok(current)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
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

    fn make_test_system() -> VCASystem {
        let (slot, slot_type) = make_test_slot();
        VCASystem::new(slot, slot_type).unwrap()
    }

    #[test]
    fn stream_empty_has_length_zero() {
        let stream = DeltaStream::empty();
        assert_eq!(stream.len(), 0);
    }

    #[test]
    fn stream_singleton_has_length_one() {
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: SlotId(999),
            t: slot_type,
        };
        let stream = DeltaStream::singleton(transition);
        assert_eq!(stream.len(), 1);
    }

    #[test]
    fn stream_append_increases_length() {
        let mut stream = DeltaStream::empty();
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: SlotId(999),
            t: slot_type,
        };
        let initial_len = stream.len();
        stream.append(transition);
        assert_eq!(stream.len(), initial_len + 1);
    }

    #[test]
    fn stream_concat_produces_combined_length() {
        let (_, slot_type) = make_test_slot();
        let transition1 = Transition::InsertSlot {
            v: SlotId(999),
            t: slot_type.clone(),
        };
        let transition2 = Transition::InsertSlot {
            v: SlotId(998),
            t: slot_type,
        };
        let stream1 = DeltaStream::singleton(transition1);
        let stream2 = DeltaStream::singleton(transition2);
        let combined = stream1.concat(stream2);
        assert_eq!(combined.len(), 2);
    }

    #[test]
    fn apply_stream_empty_returns_initial_unchanged() {
        let initial = make_test_system();
        let stream = DeltaStream::empty();
        let result = apply_stream(&stream, &initial).unwrap();
        assert_eq!(result.slots, initial.slots);
        assert_eq!(result.relations, initial.relations);
        assert_eq!(result.types, initial.types);
    }

    #[test]
    fn apply_stream_single_valid_transition_applies_correctly() {
        let initial = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let stream = DeltaStream::singleton(transition);
        let result = apply_stream(&stream, &initial).unwrap();
        assert!(result.contains_slot(new_slot));
        assert_eq!(result.slot_count(), initial.slot_count() + 1);
    }

    #[test]
    fn apply_stream_sequence_applies_in_order() {
        let initial = make_test_system();
        let slot1 = SlotId(999);
        let slot2 = SlotId(998);
        let (_, slot_type) = make_test_slot();
        let transition1 = Transition::InsertSlot {
            v: slot1,
            t: slot_type.clone(),
        };
        let transition2 = Transition::InsertSlot {
            v: slot2,
            t: slot_type,
        };
        let mut stream = DeltaStream::empty();
        stream.append(transition1);
        stream.append(transition2);
        let result = apply_stream(&stream, &initial).unwrap();
        assert!(result.contains_slot(slot1));
        assert!(result.contains_slot(slot2));
        assert_eq!(result.slot_count(), initial.slot_count() + 2);
    }

    #[test]
    fn apply_stream_invalid_transition_returns_error_with_index() {
        let initial = make_test_system();
        let (slot, slot_type) = make_test_slot();
        let invalid_transition = Transition::InsertSlot {
            v: slot,
            t: slot_type,
        };
        let stream = DeltaStream::singleton(invalid_transition);
        let result = apply_stream(&stream, &initial);
        assert!(result.is_err());
        if let Err(StreamError::TransitionFailed { index, .. }) = result {
            assert_eq!(index, 0);
        } else {
            panic!("expected TransitionFailed error");
        }
    }

    #[test]
    fn apply_stream_transitions_after_failure_not_applied() {
        let initial = make_test_system();
        let (slot, slot_type) = make_test_slot();
        let invalid_transition = Transition::InsertSlot {
            v: slot,
            t: slot_type.clone(),
        };
        let new_slot = SlotId(999);
        let valid_transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let mut stream = DeltaStream::empty();
        stream.append(invalid_transition);
        stream.append(valid_transition);
        let result = apply_stream(&stream, &initial);
        assert!(result.is_err());
        let final_system = initial;
        assert!(!final_system.contains_slot(new_slot));
    }

    #[test]
    fn apply_stream_with_callback_invokes_callback_per_transition() {
        let initial = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let stream = DeltaStream::singleton(transition);
        let mut callback_count = 0;
        let result =
            apply_stream_with_callback(&stream, &initial, |index, _transition, _system| {
                callback_count += 1;
                assert_eq!(index, 0);
                Ok(())
            })
            .unwrap();
        assert_eq!(callback_count, 1);
        assert!(result.contains_slot(new_slot));
    }

    #[test]
    fn apply_stream_with_callback_receives_correct_parameters() {
        let initial = make_test_system();
        let slot1 = SlotId(999);
        let slot2 = SlotId(998);
        let (_, slot_type) = make_test_slot();
        let transition1 = Transition::InsertSlot {
            v: slot1,
            t: slot_type.clone(),
        };
        let transition2 = Transition::InsertSlot {
            v: slot2,
            t: slot_type,
        };
        let mut stream = DeltaStream::empty();
        stream.append(transition1);
        stream.append(transition2);
        let mut indices = Vec::new();
        let result = apply_stream_with_callback(&stream, &initial, |index, _transition, system| {
            indices.push(index);
            assert!(system.contains_slot(SlotId(1)));
            if index == 0 {
                assert!(!system.contains_slot(slot1));
            } else if index == 1 {
                assert!(system.contains_slot(slot1));
            }
            Ok(())
        })
        .unwrap();
        assert_eq!(indices, vec![0, 1]);
        assert!(result.contains_slot(slot1));
        assert!(result.contains_slot(slot2));
    }

    #[test]
    fn apply_stream_with_callback_error_propagates() {
        let initial = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let stream = DeltaStream::singleton(transition);
        let result =
            apply_stream_with_callback(&stream, &initial, |_index, _transition, _system| {
                Err(StreamError::TransitionFailed {
                    index: 0,
                    error: TransitionError::PreconditionFailed("test error".to_string()),
                })
            });
        assert!(result.is_err());
    }

    #[test]
    fn apply_stream_with_callback_can_be_used_for_progress_reporting() {
        let initial = make_test_system();
        let (_, slot_type) = make_test_slot();
        let transition1 = Transition::InsertSlot {
            v: SlotId(999),
            t: slot_type.clone(),
        };
        let transition2 = Transition::InsertSlot {
            v: SlotId(998),
            t: slot_type.clone(),
        };
        let transition3 = Transition::InsertSlot {
            v: SlotId(997),
            t: slot_type,
        };
        let mut stream = DeltaStream::empty();
        stream.append(transition1);
        stream.append(transition2);
        stream.append(transition3);
        let mut progress = Vec::new();
        let result = apply_stream_with_callback(&stream, &initial, |index, _transition, system| {
            progress.push((index, system.slot_count()));
            Ok(())
        })
        .unwrap();
        assert_eq!(progress.len(), 3);
        assert_eq!(progress[0], (0, 1));
        assert_eq!(progress[1], (1, 2));
        assert_eq!(progress[2], (2, 3));
        assert_eq!(result.slot_count(), 4);
    }
}

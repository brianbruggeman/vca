use crate::system::VCASystem;
use crate::transitions::{Transition, TransitionError};
use futures::future;
use thiserror::Error;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DeltaStream(pub Vec<Transition>);

#[derive(Error, Debug, PartialEq, Eq)]
pub enum StreamError {
    #[error("transition at index {index} failed: {error:?}")]
    TransitionFailed {
        index: usize,
        error: TransitionError,
    },
}

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

pub async fn apply_stream(
    stream: &DeltaStream,
    initial: &VCASystem,
) -> Result<VCASystem, StreamError> {
    let mut current = initial.clone();
    for (index, transition) in stream.0.iter().enumerate() {
        future::ready(()).await;
        current = transition
            .apply(&current)
            .map_err(|error| StreamError::TransitionFailed { index, error })?;
    }
    Ok(current)
}

pub async fn apply_stream_with_callback<F, Fut>(
    stream: &DeltaStream,
    initial: &VCASystem,
    mut on_transition: F,
) -> Result<VCASystem, StreamError>
where
    F: FnMut(usize, &Transition, &VCASystem) -> Fut,
    Fut: std::future::Future<Output = Result<(), StreamError>>,
{
    let mut current = initial.clone();
    for (index, transition) in stream.0.iter().enumerate() {
        on_transition(index, transition, &current).await?;
        current = transition
            .apply(&current)
            .map_err(|error| StreamError::TransitionFailed { index, error })?;
    }
    Ok(current)
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

    #[tokio::test]
    async fn apply_stream_empty_returns_initial_unchanged() {
        let initial = make_test_system();
        let stream = DeltaStream::empty();
        let result = apply_stream(&stream, &initial).await.unwrap();
        assert_eq!(result.slots, initial.slots);
        assert_eq!(result.relations, initial.relations);
        assert_eq!(result.types, initial.types);
    }

    #[tokio::test]
    async fn apply_stream_single_valid_transition_applies_correctly() {
        let initial = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let stream = DeltaStream::singleton(transition);
        let result = apply_stream(&stream, &initial).await.unwrap();
        assert!(result.contains_slot(new_slot));
        assert_eq!(result.slot_count(), initial.slot_count() + 1);
    }

    #[tokio::test]
    async fn apply_stream_sequence_applies_in_order() {
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
        let result = apply_stream(&stream, &initial).await.unwrap();
        assert!(result.contains_slot(slot1));
        assert!(result.contains_slot(slot2));
        assert_eq!(result.slot_count(), initial.slot_count() + 2);
    }

    #[tokio::test]
    async fn apply_stream_invalid_transition_returns_error_with_index() {
        let initial = make_test_system();
        let (slot, slot_type) = make_test_slot();
        let invalid_transition = Transition::InsertSlot {
            v: slot,
            t: slot_type,
        };
        let stream = DeltaStream::singleton(invalid_transition);
        let result = apply_stream(&stream, &initial).await;
        assert!(result.is_err());
        if let Err(StreamError::TransitionFailed { index, .. }) = result {
            assert_eq!(index, 0);
        } else {
            panic!("expected TransitionFailed error");
        }
    }

    #[tokio::test]
    async fn apply_stream_transitions_after_failure_not_applied() {
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
        let result = apply_stream(&stream, &initial).await;
        assert!(result.is_err());
        let final_system = initial;
        assert!(!final_system.contains_slot(new_slot));
    }

    #[tokio::test]
    async fn apply_stream_with_callback_invokes_callback_per_transition() {
        let initial = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let stream = DeltaStream::singleton(transition);
        let callback_count = std::cell::Cell::new(0);
        let result =
            apply_stream_with_callback(&stream, &initial, |index, _transition, _system| {
                let count = callback_count.get();
                callback_count.set(count + 1);
                async move {
                    assert_eq!(index, 0);
                    Ok(())
                }
            })
            .await
            .unwrap();
        assert_eq!(callback_count.get(), 1);
        assert!(result.contains_slot(new_slot));
    }

    #[tokio::test]
    async fn apply_stream_with_callback_receives_correct_parameters() {
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
            let system_clone = system.clone();
            let slot1_clone = slot1;
            async move {
                assert!(system_clone.contains_slot(SlotId(1)));
                if index == 0 {
                    assert!(!system_clone.contains_slot(slot1_clone));
                } else if index == 1 {
                    assert!(system_clone.contains_slot(slot1_clone));
                }
                Ok(())
            }
        })
        .await
        .unwrap();
        assert_eq!(indices, vec![0, 1]);
        assert!(result.contains_slot(slot1));
        assert!(result.contains_slot(slot2));
    }

    #[tokio::test]
    async fn apply_stream_with_callback_error_propagates() {
        let initial = make_test_system();
        let new_slot = SlotId(999);
        let (_, slot_type) = make_test_slot();
        let transition = Transition::InsertSlot {
            v: new_slot,
            t: slot_type,
        };
        let stream = DeltaStream::singleton(transition);
        let result = apply_stream_with_callback(
            &stream,
            &initial,
            |_index, _transition, _system| async move {
                Err(StreamError::TransitionFailed {
                    index: 0,
                    error: TransitionError::PreconditionFailed("test error".to_string()),
                })
            },
        )
        .await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn apply_stream_with_callback_can_be_used_for_progress_reporting() {
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
        let progress = std::sync::Arc::new(std::sync::Mutex::new(Vec::new()));
        let progress_clone = progress.clone();
        let result =
            apply_stream_with_callback(&stream, &initial, move |index, _transition, system| {
                let progress = progress_clone.clone();
                let slot_count = system.slot_count();
                async move {
                    let mut progress = progress.lock().unwrap();
                    progress.push((index, slot_count));
                    Ok(())
                }
            })
            .await
            .unwrap();
        let progress = progress.lock().unwrap();
        assert_eq!(progress.len(), 3);
        assert_eq!(progress[0], (0, 1));
        assert_eq!(progress[1], (1, 2));
        assert_eq!(progress[2], (2, 3));
        assert_eq!(result.slot_count(), 4);
    }
}

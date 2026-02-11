//! Verified Computation Algebra (VCA) — a unified framework combining structure,
//! computation, and specification in a single 4-tuple `(V, A, τ, ℛ)`.
//!
//! VCA provides:
//! - **L0**: λ-calculus encoding (terms as slots, β-reduction as transitions)
//! - **L1**: Transition primitives with CRDT replay semantics
//! - **L2**: Temporal logic operators (□, ◇, U) over tower states
//! - **Tower**: Infinite stratified meta-reasoning with coinductive coherence

pub mod admissibility;
pub mod coherence;
pub mod constraint;
pub mod core;
pub mod dimension;
pub mod independence;
pub mod lambda;
pub mod registry;
pub mod relation;
pub mod replay;
pub mod sla;
pub mod slot;
pub mod stratification;
pub mod streams;
pub mod system;
pub mod temporal;
pub mod tower;
pub mod transitions;
pub mod types;

pub use admissibility::{
    InterpretAny, InterpretEq, InterpretNone, InterpretPatternMatch, Interpretation, admits,
    interpretation_for, is_admissible,
};
pub use coherence::{all_admissible, is_coherent};
pub use constraint::{Constraint, ConstraintId, UpperBound};
pub use core::{core, core_r, core_star};
pub use dimension::{DimValue, Dimension, ParametricSlotType, StandardDimensions, TypeSpace};
pub use independence::{Location, is_independent, read_set, write_set};
pub use lambda::{LambdaError, beta_reduce, encode_abs, encode_app, encode_var};
pub use registry::KindRegistry;
pub use relation::{PosIndex, Relation};
pub use replay::{
    ReplayError, ReplicaId, Transaction, VectorClock, eval, replay, sort_transactions, tx_cmp,
    vc_cmp,
};
pub use sla::{SLA, StatePredicate, check_sla};
pub use slot::SlotId;
pub use stratification::{Level, system_level};
pub use streams::{DeltaStream, StreamError, apply_stream, apply_stream_with_callback};
pub use system::{RuleRef, SystemError, VCASystem};
pub use temporal::TemporalFormula;
pub use tower::{Tower, TowerError};
pub use transitions::{Transition, TransitionError, apply_transition};
pub use types::{
    Affinity, Family, Kind, LambdaKind, Layer, SlotType, TypeId, TypeMeta, affinity_matches,
    family_matches, kind_matches, layer_matches, type_matches,
};

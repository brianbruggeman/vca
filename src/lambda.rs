use crate::relation::PosIndex;
use crate::slot::SlotId;
use crate::system::VCASystem;
use crate::transitions::Transition;
use crate::types::{
    Affinity, Family, Kind, LambdaKind, Layer, SlotType, TypeId, TypeMeta, UpperBound,
};

const ABS_DISCRIMINANT: u64 = 0xabcd;
const APP_DISCRIMINANT: u64 = 0xdcba;
/// Errors from L0 λ-calculus operations.
#[derive(Debug, PartialEq, Eq)]
pub enum LambdaError {
    SlotNotFound { slot_id: SlotId },
    NotLambdaTerm { slot_id: SlotId },
    NotApplication { slot_id: SlotId },
    NotAbstraction { slot_id: SlotId },
    MissingFuncRelation { app_id: SlotId, pos: PosIndex },
    MissingArgRelation { app_id: SlotId, pos: PosIndex },
    MissingBinderRelation { abs_id: SlotId, pos: PosIndex },
    MissingBodyRelation { abs_id: SlotId, pos: PosIndex },
}

impl std::fmt::Display for LambdaError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SlotNotFound { slot_id } => write!(f, "slot {slot_id:?} not found in system"),
            Self::NotLambdaTerm { slot_id } => {
                write!(f, "slot {slot_id:?} is not a lambda term")
            }
            Self::NotApplication { slot_id } => {
                write!(f, "slot {slot_id:?} is not an application")
            }
            Self::NotAbstraction { slot_id } => {
                write!(f, "slot {slot_id:?} is not an abstraction")
            }
            Self::MissingFuncRelation { app_id, pos } => {
                write!(
                    f,
                    "application {app_id:?} missing func relation at position {pos}"
                )
            }
            Self::MissingArgRelation { app_id, pos } => {
                write!(
                    f,
                    "application {app_id:?} missing arg relation at position {pos}"
                )
            }
            Self::MissingBinderRelation { abs_id, pos } => {
                write!(
                    f,
                    "abstraction {abs_id:?} missing binder relation at position {pos}"
                )
            }
            Self::MissingBodyRelation { abs_id, pos } => {
                write!(
                    f,
                    "abstraction {abs_id:?} missing body relation at position {pos}"
                )
            }
        }
    }
}

impl std::error::Error for LambdaError {}

/// Encodes a λ-variable as a slot with `Family::Lambda(Var)`.
pub fn encode_var(name: &str) -> (SlotId, SlotType) {
    let slot_id = SlotId(
        name.as_bytes()
            .iter()
            .fold(0u64, |acc, &b| acc.wrapping_mul(31).wrapping_add(b as u64)),
    );
    let slot_type = SlotType {
        family: Family::Lambda(LambdaKind::Var),
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 0,
        upper: UpperBound::Infinite,
        id: TypeId(slot_id.0),
        meta: TypeMeta::None,
    };
    (slot_id, slot_type)
}

pub fn encode_abs(binder: SlotId, body: SlotId) -> Vec<Transition> {
    let abs_id = SlotId(
        binder
            .0
            .wrapping_mul(31)
            .wrapping_add(body.0)
            .wrapping_add(ABS_DISCRIMINANT),
    );
    let abs_type = SlotType {
        family: Family::Lambda(LambdaKind::Abs),
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 2,
        upper: UpperBound::Finite(2),
        id: TypeId(abs_id.0),
        meta: TypeMeta::None,
    };
    vec![
        Transition::InsertSlot {
            v: abs_id,
            t: abs_type,
        },
        Transition::Attach {
            u: abs_id,
            v: binder,
            i: 0,
        },
        Transition::Attach {
            u: abs_id,
            v: body,
            i: 1,
        },
    ]
}

pub fn encode_app(func: SlotId, arg: SlotId) -> Vec<Transition> {
    let app_id = SlotId(
        func.0
            .wrapping_mul(31)
            .wrapping_add(arg.0)
            .wrapping_add(APP_DISCRIMINANT),
    );
    let app_type = SlotType {
        family: Family::Lambda(LambdaKind::App),
        kind: Kind::Any,
        layer: Layer::N(0),
        affinity: Affinity::Strict,
        lower: 2,
        upper: UpperBound::Finite(2),
        id: TypeId(app_id.0),
        meta: TypeMeta::None,
    };
    vec![
        Transition::InsertSlot {
            v: app_id,
            t: app_type,
        },
        Transition::Attach {
            u: app_id,
            v: func,
            i: 0,
        },
        Transition::Attach {
            u: app_id,
            v: arg,
            i: 1,
        },
    ]
}

pub fn beta_reduce(app_slot: SlotId, system: &VCASystem) -> Result<Vec<Transition>, LambdaError> {
    if !system.contains_slot(app_slot) {
        return Err(LambdaError::SlotNotFound { slot_id: app_slot });
    }

    let app_type = system
        .type_of(app_slot)
        .ok_or(LambdaError::SlotNotFound { slot_id: app_slot })?;

    match app_type.family {
        Family::Lambda(LambdaKind::App) => {}
        _ => return Err(LambdaError::NotApplication { slot_id: app_slot }),
    }

    let func_rel = system
        .relations
        .iter()
        .find(|r| r.source == app_slot && r.position == 0)
        .ok_or(LambdaError::MissingFuncRelation {
            app_id: app_slot,
            pos: 0,
        })?;

    let arg_rel = system
        .relations
        .iter()
        .find(|r| r.source == app_slot && r.position == 1)
        .ok_or(LambdaError::MissingArgRelation {
            app_id: app_slot,
            pos: 1,
        })?;

    let func_slot = func_rel.target;
    let arg_slot = arg_rel.target;

    let func_type = system
        .type_of(func_slot)
        .ok_or(LambdaError::SlotNotFound { slot_id: func_slot })?;

    match func_type.family {
        Family::Lambda(LambdaKind::Abs) => {}
        _ => return Err(LambdaError::NotAbstraction { slot_id: func_slot }),
    }

    let binder_rel = system
        .relations
        .iter()
        .find(|r| r.source == func_slot && r.position == 0)
        .ok_or(LambdaError::MissingBinderRelation {
            abs_id: func_slot,
            pos: 0,
        })?;

    let body_rel = system
        .relations
        .iter()
        .find(|r| r.source == func_slot && r.position == 1)
        .ok_or(LambdaError::MissingBodyRelation {
            abs_id: func_slot,
            pos: 1,
        })?;

    let binder_slot = binder_rel.target;
    let body_slot = body_rel.target;

    let mut transitions = vec![
        Transition::Detach {
            u: app_slot,
            v: func_slot,
            i: 0,
        },
        Transition::Detach {
            u: app_slot,
            v: arg_slot,
            i: 1,
        },
        Transition::Detach {
            u: func_slot,
            v: binder_slot,
            i: 0,
        },
        Transition::Detach {
            u: func_slot,
            v: body_slot,
            i: 1,
        },
    ];

    for rel in system.relations.iter() {
        if rel.target == binder_slot && rel.source != func_slot {
            transitions.push(Transition::Detach {
                u: rel.source,
                v: binder_slot,
                i: rel.position,
            });
            transitions.push(Transition::Attach {
                u: rel.source,
                v: arg_slot,
                i: rel.position,
            });
        }
    }

    transitions.push(Transition::DeleteSlot { v: app_slot });
    transitions.push(Transition::DeleteSlot { v: func_slot });

    Ok(transitions)
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
impl Transition {
    fn as_insert_slot(&self) -> Option<(SlotId, &SlotType)> {
        match self {
            Transition::InsertSlot { v, t } => Some((*v, t)),
            _ => None,
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::system::RuleRef;
    use crate::transitions::apply_transition;

    fn create_test_system() -> VCASystem {
        let (slot_id, slot_type) = encode_var("_temp");
        let mut system = VCASystem::new(slot_id, slot_type).expect("test system should be valid");

        let rule_slot = SlotId(999999);
        let rule_type = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(999999),
            meta: TypeMeta::None,
        };
        system.slots.push(rule_slot);
        system.types.insert(rule_slot, rule_type);
        system.rule_ref = RuleRef::SelfRef;
        system
    }

    #[test]
    fn encode_var_creates_slot_with_lambda_var_family() {
        let (_slot_id, slot_type) = encode_var("x");
        assert_eq!(slot_type.family, Family::Lambda(LambdaKind::Var));
        assert_eq!(slot_type.kind, Kind::Any);
        assert_eq!(slot_type.layer, Layer::N(0));
    }

    #[test]
    fn encode_abs_creates_abstraction_with_relations() {
        let (binder_id, _binder_type) = encode_var("x");
        let (body_id, _body_type) = encode_var("y");
        let transitions = encode_abs(binder_id, body_id);

        assert_eq!(transitions.len(), 3);
        match &transitions[0] {
            Transition::InsertSlot { v, t } => {
                assert_eq!(t.family, Family::Lambda(LambdaKind::Abs));
                let abs_id = *v;
                match &transitions[1] {
                    Transition::Attach { u, v, i } => {
                        assert_eq!(*u, abs_id);
                        assert_eq!(*v, binder_id);
                        assert_eq!(*i, 0);
                    }
                    _ => panic!("expected Attach transition"),
                }
                match &transitions[2] {
                    Transition::Attach { u, v, i } => {
                        assert_eq!(*u, abs_id);
                        assert_eq!(*v, body_id);
                        assert_eq!(*i, 1);
                    }
                    _ => panic!("expected Attach transition"),
                }
            }
            _ => panic!("expected InsertSlot transition"),
        }
    }

    #[test]
    fn encode_app_creates_application_with_relations() {
        let (func_id, _) = encode_var("f");
        let (arg_id, _) = encode_var("x");
        let transitions = encode_app(func_id, arg_id);

        assert_eq!(transitions.len(), 3);
        match &transitions[0] {
            Transition::InsertSlot { v, t } => {
                assert_eq!(t.family, Family::Lambda(LambdaKind::App));
                let app_id = *v;
                match &transitions[1] {
                    Transition::Attach { u, v, i } => {
                        assert_eq!(*u, app_id);
                        assert_eq!(*v, func_id);
                        assert_eq!(*i, 0);
                    }
                    _ => panic!("expected Attach transition"),
                }
                match &transitions[2] {
                    Transition::Attach { u, v, i } => {
                        assert_eq!(*u, app_id);
                        assert_eq!(*v, arg_id);
                        assert_eq!(*i, 1);
                    }
                    _ => panic!("expected Attach transition"),
                }
            }
            _ => panic!("expected InsertSlot transition"),
        }
    }

    #[test]
    fn encode_identity_function_has_correct_structure() {
        let (x_id, x_type) = encode_var("x");
        let mut system = create_test_system();
        system = apply_transition(&Transition::InsertSlot { v: x_id, t: x_type }, &system)
            .expect("insert should succeed");

        let abs_transitions = encode_abs(x_id, x_id);
        for t in &abs_transitions {
            system = apply_transition(t, &system).expect("transition should succeed");
        }

        let abs_slot = abs_transitions[0]
            .as_insert_slot()
            .expect("first transition should be InsertSlot")
            .0;

        let relations: Vec<_> = system
            .relations
            .iter()
            .filter(|r| r.source == abs_slot)
            .collect();

        assert_eq!(relations.len(), 2);
        assert!(
            relations
                .iter()
                .any(|r| r.target == x_id && r.position == 0)
        );
        assert!(
            relations
                .iter()
                .any(|r| r.target == x_id && r.position == 1)
        );
    }

    #[test]
    fn encode_application_has_correct_structure() {
        let (x_id, x_type) = encode_var("x");
        let (y_id, y_type) = encode_var("y");
        let mut system = create_test_system();

        system = apply_transition(&Transition::InsertSlot { v: x_id, t: x_type }, &system)
            .expect("insert should succeed");
        system = apply_transition(&Transition::InsertSlot { v: y_id, t: y_type }, &system)
            .expect("insert should succeed");

        let abs_transitions = encode_abs(x_id, x_id);
        for t in &abs_transitions {
            system = apply_transition(t, &system).expect("transition should succeed");
        }

        let abs_slot = abs_transitions[0]
            .as_insert_slot()
            .expect("first transition should be InsertSlot")
            .0;

        let app_transitions = encode_app(abs_slot, y_id);
        for t in &app_transitions {
            system = apply_transition(t, &system).expect("transition should succeed");
        }

        let app_slot = app_transitions[0]
            .as_insert_slot()
            .expect("first transition should be InsertSlot")
            .0;

        let relations: Vec<_> = system
            .relations
            .iter()
            .filter(|r| r.source == app_slot)
            .collect();

        assert_eq!(relations.len(), 2);
        assert!(
            relations
                .iter()
                .any(|r| r.target == abs_slot && r.position == 0)
        );
        assert!(
            relations
                .iter()
                .any(|r| r.target == y_id && r.position == 1)
        );
    }

    #[test]
    fn beta_reduce_identity_application_produces_arg() {
        let (x_id, x_type) = encode_var("x");
        let (y_id, y_type) = encode_var("y");
        let mut system = create_test_system();

        system = apply_transition(&Transition::InsertSlot { v: x_id, t: x_type }, &system)
            .expect("insert should succeed");
        system = apply_transition(&Transition::InsertSlot { v: y_id, t: y_type }, &system)
            .expect("insert should succeed");

        let abs_transitions = encode_abs(x_id, x_id);
        for t in &abs_transitions {
            system = apply_transition(t, &system).expect("transition should succeed");
        }

        let abs_slot = abs_transitions[0]
            .as_insert_slot()
            .expect("first transition should be InsertSlot")
            .0;

        let app_transitions = encode_app(abs_slot, y_id);
        for t in &app_transitions {
            system = apply_transition(t, &system).expect("transition should succeed");
        }

        let app_slot = app_transitions[0]
            .as_insert_slot()
            .expect("first transition should be InsertSlot")
            .0;

        let beta_transitions =
            beta_reduce(app_slot, &system).expect("beta reduction should succeed");

        for t in &beta_transitions {
            system = apply_transition(t, &system).expect("transition should succeed");
        }

        assert!(!system.contains_slot(app_slot));
        assert!(!system.contains_slot(abs_slot));
        assert!(system.contains_slot(y_id));
        assert!(system.contains_slot(x_id));
    }

    #[test]
    fn beta_reduce_returns_error_for_nonexistent_slot() {
        let system = create_test_system();
        let result = beta_reduce(SlotId(999), &system);
        assert_eq!(
            result,
            Err(LambdaError::SlotNotFound {
                slot_id: SlotId(999)
            })
        );
    }

    #[test]
    fn beta_reduce_returns_error_for_non_application() {
        let (x_id, x_type) = encode_var("x");
        let mut system = create_test_system();
        system = apply_transition(&Transition::InsertSlot { v: x_id, t: x_type }, &system)
            .expect("insert should succeed");

        let result = beta_reduce(x_id, &system);
        assert_eq!(result, Err(LambdaError::NotApplication { slot_id: x_id }));
    }
}

use crate::system::VCASystem;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TemporalFormula<P> {
    Prop(P),
    Always(Box<TemporalFormula<P>>),
    Eventually(Box<TemporalFormula<P>>),
    Until(Box<TemporalFormula<P>>, Box<TemporalFormula<P>>),
    Next(Box<TemporalFormula<P>>),
    And(Box<TemporalFormula<P>>, Box<TemporalFormula<P>>),
    Or(Box<TemporalFormula<P>>, Box<TemporalFormula<P>>),
    Not(Box<TemporalFormula<P>>),
}

impl<P> TemporalFormula<P> {
    pub fn always(phi: TemporalFormula<P>) -> Self {
        TemporalFormula::Always(Box::new(phi))
    }

    pub fn eventually(phi: TemporalFormula<P>) -> Self {
        TemporalFormula::Eventually(Box::new(phi))
    }

    pub fn until(phi: TemporalFormula<P>, psi: TemporalFormula<P>) -> Self {
        TemporalFormula::Until(Box::new(phi), Box::new(psi))
    }

    pub fn next(phi: TemporalFormula<P>) -> Self {
        TemporalFormula::Next(Box::new(phi))
    }

    pub fn and(phi: TemporalFormula<P>, psi: TemporalFormula<P>) -> Self {
        TemporalFormula::And(Box::new(phi), Box::new(psi))
    }

    pub fn or(phi: TemporalFormula<P>, psi: TemporalFormula<P>) -> Self {
        TemporalFormula::Or(Box::new(phi), Box::new(psi))
    }

    #[allow(clippy::should_implement_trait)]
    pub fn not(phi: TemporalFormula<P>) -> Self {
        TemporalFormula::Not(Box::new(phi))
    }

    pub fn check_up_to<F>(&self, trace: &[VCASystem], prop_check: F, depth: usize) -> bool
    where
        F: Fn(&VCASystem, &P) -> bool,
        P: Clone,
    {
        if trace.is_empty() || depth == 0 {
            return false;
        }

        let max_idx = (trace.len() - 1).min(depth);
        self.check_at(trace, &prop_check, 0, max_idx)
    }

    fn check_at<F>(&self, trace: &[VCASystem], prop_check: &F, start: usize, end: usize) -> bool
    where
        F: Fn(&VCASystem, &P) -> bool,
        P: Clone,
    {
        match self {
            TemporalFormula::Prop(p) => {
                if start > end || start >= trace.len() {
                    return false;
                }
                prop_check(&trace[start], p)
            }
            TemporalFormula::Always(phi) => {
                for i in start..=end.min(trace.len().saturating_sub(1)) {
                    if !phi.check_at(trace, prop_check, i, end) {
                        return false;
                    }
                }
                true
            }
            TemporalFormula::Eventually(phi) => {
                for i in start..=end.min(trace.len().saturating_sub(1)) {
                    if phi.check_at(trace, prop_check, i, end) {
                        return true;
                    }
                }
                false
            }
            TemporalFormula::Until(phi, psi) => {
                for j in start..=end.min(trace.len().saturating_sub(1)) {
                    if psi.check_at(trace, prop_check, j, end) {
                        let mut all_phi = true;
                        if j == start {
                            if !phi.check_at(trace, prop_check, start, end) {
                                all_phi = false;
                            }
                        } else {
                            for i in start..j {
                                if !phi.check_at(trace, prop_check, i, end) {
                                    all_phi = false;
                                    break;
                                }
                            }
                        }
                        if all_phi {
                            return true;
                        }
                    }
                }
                false
            }
            TemporalFormula::Next(phi) => {
                if start >= end || start + 1 >= trace.len() {
                    return false;
                }
                phi.check_at(trace, prop_check, start + 1, end)
            }
            TemporalFormula::And(phi, psi) => {
                phi.check_at(trace, prop_check, start, end)
                    && psi.check_at(trace, prop_check, start, end)
            }
            TemporalFormula::Or(phi, psi) => {
                phi.check_at(trace, prop_check, start, end)
                    || psi.check_at(trace, prop_check, start, end)
            }
            TemporalFormula::Not(phi) => !phi.check_at(trace, prop_check, start, end),
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use crate::slot::SlotId;
    use crate::types::{Affinity, Family, Kind, Layer, SlotType, TypeId, TypeMeta, UpperBound};

    fn make_test_system() -> VCASystem {
        let slot_id = SlotId(1);
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        VCASystem::new(slot_id, slot_type).expect("test system should be valid")
    }

    #[test]
    fn prop_wraps_predicate() {
        let formula = TemporalFormula::Prop(42);
        match formula {
            TemporalFormula::Prop(n) => assert_eq!(n, 42),
            _ => panic!("expected Prop variant"),
        }
    }

    #[test]
    fn always_represents_box() {
        let inner = TemporalFormula::Prop(true);
        let formula = TemporalFormula::Always(Box::new(inner.clone()));
        match formula {
            TemporalFormula::Always(boxed) => assert_eq!(*boxed, inner),
            _ => panic!("expected Always variant"),
        }
    }

    #[test]
    fn eventually_represents_diamond() {
        let inner = TemporalFormula::Prop(true);
        let formula = TemporalFormula::Eventually(Box::new(inner.clone()));
        match formula {
            TemporalFormula::Eventually(boxed) => assert_eq!(*boxed, inner),
            _ => panic!("expected Eventually variant"),
        }
    }

    #[test]
    fn until_represents_u() {
        let phi = TemporalFormula::Prop(true);
        let psi = TemporalFormula::Prop(false);
        let formula = TemporalFormula::Until(Box::new(phi.clone()), Box::new(psi.clone()));
        match formula {
            TemporalFormula::Until(boxed_phi, boxed_psi) => {
                assert_eq!(*boxed_phi, phi);
                assert_eq!(*boxed_psi, psi);
            }
            _ => panic!("expected Until variant"),
        }
    }

    #[test]
    fn next_represents_circle() {
        let inner = TemporalFormula::Prop(true);
        let formula = TemporalFormula::Next(Box::new(inner.clone()));
        match formula {
            TemporalFormula::Next(boxed) => assert_eq!(*boxed, inner),
            _ => panic!("expected Next variant"),
        }
    }

    #[test]
    fn and_combines_formulas() {
        let phi = TemporalFormula::Prop(true);
        let psi = TemporalFormula::Prop(false);
        let formula = TemporalFormula::And(Box::new(phi.clone()), Box::new(psi.clone()));
        match formula {
            TemporalFormula::And(boxed_phi, boxed_psi) => {
                assert_eq!(*boxed_phi, phi);
                assert_eq!(*boxed_psi, psi);
            }
            _ => panic!("expected And variant"),
        }
    }

    #[test]
    fn or_combines_formulas() {
        let phi = TemporalFormula::Prop(true);
        let psi = TemporalFormula::Prop(false);
        let formula = TemporalFormula::Or(Box::new(phi.clone()), Box::new(psi.clone()));
        match formula {
            TemporalFormula::Or(boxed_phi, boxed_psi) => {
                assert_eq!(*boxed_phi, phi);
                assert_eq!(*boxed_psi, psi);
            }
            _ => panic!("expected Or variant"),
        }
    }

    #[test]
    fn not_negates_formula() {
        let inner = TemporalFormula::Prop(true);
        let formula = TemporalFormula::Not(Box::new(inner.clone()));
        match formula {
            TemporalFormula::Not(boxed) => assert_eq!(*boxed, inner),
            _ => panic!("expected Not variant"),
        }
    }

    #[test]
    fn always_constructor_returns_always() {
        let inner = TemporalFormula::Prop(42);
        let formula = TemporalFormula::always(inner.clone());
        match formula {
            TemporalFormula::Always(boxed) => assert_eq!(*boxed, inner),
            _ => panic!("expected Always variant"),
        }
    }

    #[test]
    fn eventually_constructor_returns_eventually() {
        let inner = TemporalFormula::Prop(42);
        let formula = TemporalFormula::eventually(inner.clone());
        match formula {
            TemporalFormula::Eventually(boxed) => assert_eq!(*boxed, inner),
            _ => panic!("expected Eventually variant"),
        }
    }

    #[test]
    fn until_constructor_returns_until() {
        let phi = TemporalFormula::Prop(true);
        let psi = TemporalFormula::Prop(false);
        let formula = TemporalFormula::until(phi.clone(), psi.clone());
        match formula {
            TemporalFormula::Until(boxed_phi, boxed_psi) => {
                assert_eq!(*boxed_phi, phi);
                assert_eq!(*boxed_psi, psi);
            }
            _ => panic!("expected Until variant"),
        }
    }

    #[test]
    fn next_constructor_returns_next() {
        let inner = TemporalFormula::Prop(42);
        let formula = TemporalFormula::next(inner.clone());
        match formula {
            TemporalFormula::Next(boxed) => assert_eq!(*boxed, inner),
            _ => panic!("expected Next variant"),
        }
    }

    #[test]
    fn and_constructor_returns_and() {
        let phi = TemporalFormula::Prop(true);
        let psi = TemporalFormula::Prop(false);
        let formula = TemporalFormula::and(phi.clone(), psi.clone());
        match formula {
            TemporalFormula::And(boxed_phi, boxed_psi) => {
                assert_eq!(*boxed_phi, phi);
                assert_eq!(*boxed_psi, psi);
            }
            _ => panic!("expected And variant"),
        }
    }

    #[test]
    fn or_constructor_returns_or() {
        let phi = TemporalFormula::Prop(true);
        let psi = TemporalFormula::Prop(false);
        let formula = TemporalFormula::or(phi.clone(), psi.clone());
        match formula {
            TemporalFormula::Or(boxed_phi, boxed_psi) => {
                assert_eq!(*boxed_phi, phi);
                assert_eq!(*boxed_psi, psi);
            }
            _ => panic!("expected Or variant"),
        }
    }

    #[test]
    fn not_constructor_returns_not() {
        let inner = TemporalFormula::Prop(42);
        let formula = TemporalFormula::not(inner.clone());
        match formula {
            TemporalFormula::Not(boxed) => assert_eq!(*boxed, inner),
            _ => panic!("expected Not variant"),
        }
    }

    #[test]
    fn always_check_up_to_returns_true_when_all_true() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::always(TemporalFormula::Prop(true));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(result);
    }

    #[test]
    fn always_check_up_to_returns_false_when_one_false() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::always(TemporalFormula::Prop(false));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(!result);
    }

    #[test]
    fn eventually_check_up_to_returns_true_when_one_true() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::eventually(TemporalFormula::Prop(true));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(result);
    }

    #[test]
    fn eventually_check_up_to_returns_false_when_all_false() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::eventually(TemporalFormula::Prop(false));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(!result);
    }

    #[test]
    fn next_check_up_to_checks_next_index() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::next(TemporalFormula::Prop(true));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(result);
    }

    #[test]
    fn next_check_up_to_fails_when_next_false() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::next(TemporalFormula::Prop(false));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(!result);
    }

    #[test]
    fn until_check_up_to_finds_witness() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let phi = TemporalFormula::Prop(true);
        let psi = TemporalFormula::Prop(true);
        let formula = TemporalFormula::until(phi, psi);
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(result);
    }

    #[test]
    fn until_check_up_to_requires_phi_before_psi() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let phi = TemporalFormula::Prop(false);
        let psi = TemporalFormula::Prop(true);
        let formula = TemporalFormula::until(phi, psi);
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(!result);
    }

    #[test]
    fn always_check_up_to_holds_at_all_indices() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::always(TemporalFormula::Prop(true));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(result);
    }

    #[test]
    fn eventually_check_up_to_holds_at_some_index() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::eventually(TemporalFormula::Prop(true));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(result);
    }

    #[test]
    fn next_check_up_to_holds_at_index_one() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let formula = TemporalFormula::next(TemporalFormula::Prop(true));
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(result);
    }

    #[test]
    fn until_check_up_to_requires_psi_at_j_and_phi_before() {
        let trace = vec![
            make_test_system(),
            make_test_system(),
            make_test_system(),
            make_test_system(),
        ];
        let phi = TemporalFormula::Prop(true);
        let psi = TemporalFormula::Prop(true);
        let formula = TemporalFormula::until(phi, psi);
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(result);
    }

    #[test]
    fn check_up_to_empty_trace_returns_false() {
        let trace: Vec<VCASystem> = vec![];
        let formula = TemporalFormula::Prop(true);
        let result = formula.check_up_to(&trace, |_, p| *p, 3);
        assert!(!result);
    }

    #[test]
    fn check_up_to_depth_zero_returns_false() {
        let trace = vec![make_test_system()];
        let formula = TemporalFormula::Prop(true);
        let result = formula.check_up_to(&trace, |_, p| *p, 0);
        assert!(!result);
    }
}

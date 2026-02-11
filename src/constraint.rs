/// Upper bound on source count: finite or infinite.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UpperBound {
    Finite(u32),
    Infinite,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConstraintId(pub u64);

/// Lower/upper bound constraint on relation counts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Constraint {
    pub lower: u32,
    pub upper: UpperBound,
    pub id: ConstraintId,
}

impl Constraint {
    pub fn is_well_formed(&self) -> bool {
        match self.upper {
            UpperBound::Finite(upper) => self.lower <= upper,
            UpperBound::Infinite => true,
        }
    }

    pub fn upper_satisfied(&self, count: u32) -> bool {
        match self.upper {
            UpperBound::Finite(upper) => count <= upper,
            UpperBound::Infinite => true,
        }
    }

    pub fn lower_satisfied(&self, count: u32) -> bool {
        self.lower <= count
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case::lower_less_than_upper(
        Constraint {
            lower: 0,
            upper: UpperBound::Finite(5),
            id: ConstraintId(1),
        },
        true
    )]
    #[case::lower_equals_upper(
        Constraint {
            lower: 3,
            upper: UpperBound::Finite(3),
            id: ConstraintId(2),
        },
        true
    )]
    #[case::lower_greater_than_upper(
        Constraint {
            lower: 5,
            upper: UpperBound::Finite(3),
            id: ConstraintId(3),
        },
        false
    )]
    #[case::infinite_upper_bound(
        Constraint {
            lower: 100,
            upper: UpperBound::Infinite,
            id: ConstraintId(4),
        },
        true
    )]
    fn is_well_formed_cases(#[case] constraint: Constraint, #[case] expected: bool) {
        assert_eq!(constraint.is_well_formed(), expected);
    }

    #[rstest]
    #[case::count_less_than_finite_upper(UpperBound::Finite(5), 3, true)]
    #[case::count_equals_finite_upper(UpperBound::Finite(5), 5, true)]
    #[case::count_greater_than_finite_upper(UpperBound::Finite(5), 6, false)]
    #[case::infinite_upper_always_satisfied(UpperBound::Infinite, 999999, true)]
    fn upper_satisfied_cases(
        #[case] upper: UpperBound,
        #[case] count: u32,
        #[case] expected: bool,
    ) {
        let constraint = Constraint {
            lower: 0,
            upper,
            id: ConstraintId(1),
        };
        assert_eq!(constraint.upper_satisfied(count), expected);
    }

    #[rstest]
    #[case::count_equals_lower(0, 0, true)]
    #[case::count_greater_than_lower(3, 5, true)]
    #[case::count_less_than_lower(5, 3, false)]
    fn lower_satisfied_cases(#[case] lower: u32, #[case] count: u32, #[case] expected: bool) {
        let constraint = Constraint {
            lower,
            upper: UpperBound::Infinite,
            id: ConstraintId(1),
        };
        assert_eq!(constraint.lower_satisfied(count), expected);
    }
}

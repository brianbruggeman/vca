/// Slot family: the primary categorization dimension.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Family {
    Top,
    Bot,
    Rule,
    Data,
    Lambda(LambdaKind),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum LambdaKind {
    Var,
    Abs,
    App,
}

/// Interpretation selector: determines how a rule admits relations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Kind {
    Top,
    Bot,
    Any,
    None,
    PatternMatch,
    Eq,
}

/// Stratification layer in the tower.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Layer {
    Top,
    Bot,
    N(u32),
}

/// Connection mode for a slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Affinity {
    Top,
    Bot,
    Strict,
    Lax,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UpperBound {
    Finite(u32),
    Infinite,
}

/// Unique type identifier.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeId(pub u64);

/// Domain-specific metadata attached to a type (patterns, id pairs, etc.).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeMeta {
    None,
    PatternMatch {
        pattern_source: Box<SlotType>,
        pattern_target: Box<SlotType>,
    },
    Eq {
        i_eq: crate::relation::PosIndex,
        id_pairs: std::collections::HashSet<(u64, u64)>,
    },
}

impl std::hash::Hash for TypeMeta {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self {
            TypeMeta::None => 0u8.hash(state),
            TypeMeta::PatternMatch {
                pattern_source,
                pattern_target,
            } => {
                1u8.hash(state);
                pattern_source.hash(state);
                pattern_target.hash(state);
            }
            TypeMeta::Eq { i_eq, id_pairs } => {
                2u8.hash(state);
                i_eq.hash(state);
                let mut sorted_pairs: Vec<_> = id_pairs.iter().collect();
                sorted_pairs.sort();
                for pair in sorted_pairs {
                    pair.hash(state);
                }
            }
        }
    }
}

/// Complete type assignment for a slot: 8 dimensions from the parametric type space T.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SlotType {
    pub family: Family,
    pub kind: Kind,
    pub layer: Layer,
    pub affinity: Affinity,
    pub lower: u32,
    pub upper: UpperBound,
    pub id: TypeId,
    pub meta: TypeMeta,
}

impl SlotType {
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

#[deprecated(note = "use ParametricSlotType from dimension module instead")]
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LType {
    pub family: Family,
    pub kind: Kind,
    pub layer: Layer,
    pub affinity: Affinity,
    pub meta: TypeMeta,
}

#[allow(deprecated)]
impl LType {
    pub fn to_parametric_slot_type(
        &self,
        space: &crate::dimension::TypeSpace,
    ) -> Option<crate::dimension::ParametricSlotType> {
        let family_idx = space.dimension_index("family")?;
        let kind_idx = space.dimension_index("kind")?;
        let layer_idx = space.dimension_index("layer")?;
        let affinity_idx = space.dimension_index("affinity")?;

        // set unused dimensions to Top so they don't affect matching
        // (LType only uses 4 dimensions, so others are "don't care")
        let mut values = vec![crate::dimension::DimValue::Top; space.dimension_count()];

        values[family_idx] = match self.family {
            Family::Top => crate::dimension::DimValue::Top,
            Family::Bot => crate::dimension::DimValue::Bot,
            Family::Rule => crate::dimension::DimValue::Named("Rule".to_string()),
            Family::Data => crate::dimension::DimValue::Named("Data".to_string()),
            Family::Lambda(kind) => {
                let kind_str = match kind {
                    LambdaKind::Var => "Lambda::Var",
                    LambdaKind::Abs => "Lambda::Abs",
                    LambdaKind::App => "Lambda::App",
                };
                crate::dimension::DimValue::Named(kind_str.to_string())
            }
        };

        values[kind_idx] = match self.kind {
            Kind::Top => crate::dimension::DimValue::Top,
            Kind::Bot => crate::dimension::DimValue::Bot,
            Kind::Any => crate::dimension::DimValue::Named("Any".to_string()),
            Kind::None => crate::dimension::DimValue::Named("None".to_string()),
            Kind::PatternMatch => crate::dimension::DimValue::Named("PatternMatch".to_string()),
            Kind::Eq => crate::dimension::DimValue::Named("Eq".to_string()),
        };

        values[layer_idx] = match self.layer {
            Layer::Top => crate::dimension::DimValue::Top,
            Layer::Bot => crate::dimension::DimValue::Bot,
            Layer::N(n) => crate::dimension::DimValue::Num(n as u64),
        };

        values[affinity_idx] = match self.affinity {
            Affinity::Top => crate::dimension::DimValue::Top,
            Affinity::Bot => crate::dimension::DimValue::Bot,
            Affinity::Strict => crate::dimension::DimValue::Named("Strict".to_string()),
            Affinity::Lax => crate::dimension::DimValue::Named("Lax".to_string()),
        };

        Some(crate::dimension::ParametricSlotType::new(values))
    }
}

impl SlotType {
    pub fn to_parametric_slot_type(
        &self,
        space: &crate::dimension::TypeSpace,
    ) -> Option<crate::dimension::ParametricSlotType> {
        let family_idx = space.dimension_index("family")?;
        let kind_idx = space.dimension_index("kind")?;
        let layer_idx = space.dimension_index("layer")?;
        let affinity_idx = space.dimension_index("affinity")?;
        let lower_idx = space.dimension_index("lower")?;
        let upper_idx = space.dimension_index("upper")?;
        let id_idx = space.dimension_index("id")?;
        let meta_idx = space.dimension_index("meta")?;

        let mut values = vec![crate::dimension::DimValue::Bot; space.dimension_count()];

        values[family_idx] = match self.family {
            Family::Top => crate::dimension::DimValue::Top,
            Family::Bot => crate::dimension::DimValue::Bot,
            Family::Rule => crate::dimension::DimValue::Named("Rule".to_string()),
            Family::Data => crate::dimension::DimValue::Named("Data".to_string()),
            Family::Lambda(kind) => {
                let kind_str = match kind {
                    LambdaKind::Var => "Lambda::Var",
                    LambdaKind::Abs => "Lambda::Abs",
                    LambdaKind::App => "Lambda::App",
                };
                crate::dimension::DimValue::Named(kind_str.to_string())
            }
        };

        values[kind_idx] = match self.kind {
            Kind::Top => crate::dimension::DimValue::Top,
            Kind::Bot => crate::dimension::DimValue::Bot,
            Kind::Any => crate::dimension::DimValue::Named("Any".to_string()),
            Kind::None => crate::dimension::DimValue::Named("None".to_string()),
            Kind::PatternMatch => crate::dimension::DimValue::Named("PatternMatch".to_string()),
            Kind::Eq => crate::dimension::DimValue::Named("Eq".to_string()),
        };

        values[layer_idx] = match self.layer {
            Layer::Top => crate::dimension::DimValue::Top,
            Layer::Bot => crate::dimension::DimValue::Bot,
            Layer::N(n) => crate::dimension::DimValue::Num(n as u64),
        };

        values[affinity_idx] = match self.affinity {
            Affinity::Top => crate::dimension::DimValue::Top,
            Affinity::Bot => crate::dimension::DimValue::Bot,
            Affinity::Strict => crate::dimension::DimValue::Named("Strict".to_string()),
            Affinity::Lax => crate::dimension::DimValue::Named("Lax".to_string()),
        };

        values[lower_idx] = crate::dimension::DimValue::Num(self.lower as u64);

        values[upper_idx] = match self.upper {
            UpperBound::Finite(n) => crate::dimension::DimValue::Num(n as u64),
            UpperBound::Infinite => crate::dimension::DimValue::Named("Infinite".to_string()),
        };

        values[id_idx] = crate::dimension::DimValue::Num(self.id.0);

        values[meta_idx] = match &self.meta {
            TypeMeta::None => crate::dimension::DimValue::Bot,
            TypeMeta::PatternMatch { .. } | TypeMeta::Eq { .. } => {
                crate::dimension::DimValue::Named("pattern".to_string())
            }
        };

        Some(crate::dimension::ParametricSlotType::new(values))
    }
}

pub fn family_matches(pattern: Family, actual: Family) -> bool {
    match (pattern, actual) {
        (Family::Top, _) => true,
        (Family::Bot, _) => false,
        (Family::Lambda(p_kind), Family::Lambda(a_kind)) => p_kind == a_kind,
        (p, a) => p == a,
    }
}

pub fn kind_matches(pattern: Kind, actual: Kind) -> bool {
    match (pattern, actual) {
        (Kind::Top, _) => true,
        (Kind::Bot, _) => false,
        (p, a) => p == a,
    }
}

pub fn layer_matches(pattern: &Layer, actual: &Layer) -> bool {
    match (pattern, actual) {
        (Layer::Top, _) => true,
        (Layer::Bot, _) => false,
        (Layer::N(p), Layer::N(a)) => p == a,
        _ => false,
    }
}

pub fn affinity_matches(pattern: Affinity, actual: Affinity) -> bool {
    match (pattern, actual) {
        (Affinity::Top, _) => true,
        (Affinity::Bot, _) => false,
        (p, a) => p == a,
    }
}

#[allow(deprecated)]
pub fn type_matches(pattern: &LType, actual: &LType) -> bool {
    use crate::dimension::StandardDimensions;
    let space = StandardDimensions::vca();
    let pattern_parametric = match pattern.to_parametric_slot_type(&space) {
        Some(p) => p,
        None => {
            // fallback to old behavior if conversion fails
            return family_matches(pattern.family, actual.family)
                && kind_matches(pattern.kind, actual.kind)
                && layer_matches(&pattern.layer, &actual.layer)
                && affinity_matches(pattern.affinity, actual.affinity);
        }
    };
    let actual_parametric = match actual.to_parametric_slot_type(&space) {
        Some(a) => a,
        None => {
            // fallback to old behavior if conversion fails
            return family_matches(pattern.family, actual.family)
                && kind_matches(pattern.kind, actual.kind)
                && layer_matches(&pattern.layer, &actual.layer)
                && affinity_matches(pattern.affinity, actual.affinity);
        }
    };
    actual_parametric.matches(&pattern_parametric)
}

pub fn slot_type_matches(pattern: &SlotType, actual: &SlotType) -> bool {
    // slot_type_matches only checks the 4 core dimensions (family, kind, layer, affinity)
    // to maintain backward compatibility with pattern matching behavior
    // other dimensions (lower, upper, id, meta) are ignored for matching
    use crate::dimension::StandardDimensions;
    let space = StandardDimensions::vca();

    let pattern_parametric = match pattern.to_parametric_slot_type(&space) {
        Some(p) => p,
        None => {
            return family_matches(pattern.family, actual.family)
                && kind_matches(pattern.kind, actual.kind)
                && layer_matches(&pattern.layer, &actual.layer)
                && affinity_matches(pattern.affinity, actual.affinity);
        }
    };
    let actual_parametric = match actual.to_parametric_slot_type(&space) {
        Some(a) => a,
        None => {
            return family_matches(pattern.family, actual.family)
                && kind_matches(pattern.kind, actual.kind)
                && layer_matches(&pattern.layer, &actual.layer)
                && affinity_matches(pattern.affinity, actual.affinity);
        }
    };

    // only check first 4 dimensions (family, kind, layer, affinity)
    let pattern_values = pattern_parametric.values();
    let actual_values = actual_parametric.values();
    if pattern_values.len() != actual_values.len() || pattern_values.len() < 4 {
        return false;
    }

    (0..4).all(|i| match pattern_values[i] {
        crate::dimension::DimValue::Top => true,
        crate::dimension::DimValue::Bot => false,
        _ => actual_values[i] == pattern_values[i],
    })
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[rstest]
    #[case::top_matches_any(Family::Top, Family::Rule, true)]
    #[case::top_matches_data(Family::Top, Family::Data, true)]
    #[case::top_matches_lambda(Family::Top, Family::Lambda(LambdaKind::Var), true)]
    #[case::exact_match(Family::Rule, Family::Rule, true)]
    #[case::mismatch(Family::Rule, Family::Data, false)]
    #[case::bot_matches_nothing(Family::Bot, Family::Rule, false)]
    #[case::bot_not_self(Family::Bot, Family::Bot, false)]
    #[case::lambda_var_matches_var(
        Family::Lambda(LambdaKind::Var),
        Family::Lambda(LambdaKind::Var),
        true
    )]
    #[case::lambda_abs_matches_abs(
        Family::Lambda(LambdaKind::Abs),
        Family::Lambda(LambdaKind::Abs),
        true
    )]
    #[case::lambda_app_matches_app(
        Family::Lambda(LambdaKind::App),
        Family::Lambda(LambdaKind::App),
        true
    )]
    #[case::lambda_var_not_matches_abs(
        Family::Lambda(LambdaKind::Var),
        Family::Lambda(LambdaKind::Abs),
        false
    )]
    #[case::lambda_not_matches_rule(Family::Lambda(LambdaKind::Var), Family::Rule, false)]
    fn family_matches_cases(
        #[case] pattern: Family,
        #[case] actual: Family,
        #[case] expected: bool,
    ) {
        assert_eq!(family_matches(pattern, actual), expected);
    }

    #[rstest]
    #[case::top_matches_any(Kind::Top, Kind::Any, true)]
    #[case::exact_match(Kind::Any, Kind::Any, true)]
    #[case::mismatch(Kind::PatternMatch, Kind::Eq, false)]
    #[case::bot_matches_nothing(Kind::Bot, Kind::Any, false)]
    fn kind_matches_cases(#[case] pattern: Kind, #[case] actual: Kind, #[case] expected: bool) {
        assert_eq!(kind_matches(pattern, actual), expected);
    }

    #[rstest]
    #[case::top_matches_any(&Layer::Top, &Layer::N(0), true)]
    #[case::exact_match(&Layer::N(5), &Layer::N(5), true)]
    #[case::mismatch(&Layer::N(3), &Layer::N(7), false)]
    #[case::bot_matches_nothing(&Layer::Bot, &Layer::N(0), false)]
    fn layer_matches_cases(
        #[case] pattern: &Layer,
        #[case] actual: &Layer,
        #[case] expected: bool,
    ) {
        assert_eq!(layer_matches(pattern, actual), expected);
    }

    #[rstest]
    #[case::top_matches_any(Affinity::Top, Affinity::Strict, true)]
    #[case::exact_match(Affinity::Strict, Affinity::Strict, true)]
    #[case::mismatch(Affinity::Strict, Affinity::Lax, false)]
    fn affinity_matches_cases(
        #[case] pattern: Affinity,
        #[case] actual: Affinity,
        #[case] expected: bool,
    ) {
        assert_eq!(affinity_matches(pattern, actual), expected);
    }

    #[allow(deprecated)]
    #[test]
    fn type_matches_full_wildcard() {
        let pattern = LType {
            family: Family::Top,
            kind: Kind::Top,
            layer: Layer::Top,
            affinity: Affinity::Top,
            meta: TypeMeta::None,
        };
        let actual = LType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(42),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        assert!(type_matches(&pattern, &actual));
    }

    #[allow(deprecated)]
    #[test]
    fn type_matches_exact() {
        let pattern = LType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        let actual = LType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        assert!(type_matches(&pattern, &actual));
    }

    #[allow(deprecated)]
    #[test]
    fn type_matches_single_dimension_mismatch() {
        let pattern = LType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        let actual = LType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(7),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        assert!(!type_matches(&pattern, &actual));
    }

    #[allow(deprecated)]
    #[test]
    fn type_matches_mixed_wildcards() {
        let pattern = LType {
            family: Family::Top,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Top,
            meta: TypeMeta::None,
        };
        let actual1 = LType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        let actual2 = LType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Lax,
            meta: TypeMeta::None,
        };
        assert!(type_matches(&pattern, &actual1));
        assert!(type_matches(&pattern, &actual2));
    }

    #[test]
    fn slot_type_is_well_formed_lower_less_than_upper() {
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(5),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        assert!(slot_type.is_well_formed());
    }

    #[test]
    fn slot_type_is_well_formed_lower_equals_upper() {
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 3,
            upper: UpperBound::Finite(3),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        assert!(slot_type.is_well_formed());
    }

    #[test]
    fn slot_type_is_well_formed_lower_greater_than_upper() {
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 5,
            upper: UpperBound::Finite(3),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        assert!(!slot_type.is_well_formed());
    }

    #[test]
    fn slot_type_is_well_formed_infinite_upper() {
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 100,
            upper: UpperBound::Infinite,
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        assert!(slot_type.is_well_formed());
    }

    #[test]
    fn slot_type_upper_satisfied_count_less_than_finite() {
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(5),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        assert!(slot_type.upper_satisfied(3));
    }

    #[test]
    fn slot_type_upper_satisfied_count_equals_finite() {
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(5),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        assert!(slot_type.upper_satisfied(5));
    }

    #[test]
    fn slot_type_upper_satisfied_count_greater_than_finite() {
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(5),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        assert!(!slot_type.upper_satisfied(6));
    }

    #[test]
    fn slot_type_upper_satisfied_infinite_always_satisfied() {
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
        assert!(slot_type.upper_satisfied(999999));
    }

    #[allow(deprecated)]
    #[test]
    fn ltype_to_parametric_slot_type_converts_correctly() {
        let space = crate::dimension::StandardDimensions::vca();
        let ltype = LType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(5),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        let parametric = ltype
            .to_parametric_slot_type(&space)
            .expect("conversion should succeed");
        assert_eq!(
            parametric.value(space.dimension_index("family").unwrap()),
            Some(&crate::dimension::DimValue::Named("Rule".to_string()))
        );
        assert_eq!(
            parametric.value(space.dimension_index("kind").unwrap()),
            Some(&crate::dimension::DimValue::Named("Any".to_string()))
        );
        assert_eq!(
            parametric.value(space.dimension_index("layer").unwrap()),
            Some(&crate::dimension::DimValue::Num(5))
        );
        assert_eq!(
            parametric.value(space.dimension_index("affinity").unwrap()),
            Some(&crate::dimension::DimValue::Named("Strict".to_string()))
        );
    }

    #[allow(deprecated)]
    #[test]
    fn ltype_to_parametric_slot_type_with_top_values() {
        let space = crate::dimension::StandardDimensions::vca();
        let ltype = LType {
            family: Family::Top,
            kind: Kind::Top,
            layer: Layer::Top,
            affinity: Affinity::Top,
            meta: TypeMeta::None,
        };
        let parametric = ltype
            .to_parametric_slot_type(&space)
            .expect("conversion should succeed");
        assert_eq!(
            parametric.value(space.dimension_index("family").unwrap()),
            Some(&crate::dimension::DimValue::Top)
        );
        assert_eq!(
            parametric.value(space.dimension_index("kind").unwrap()),
            Some(&crate::dimension::DimValue::Top)
        );
        assert_eq!(
            parametric.value(space.dimension_index("layer").unwrap()),
            Some(&crate::dimension::DimValue::Top)
        );
        assert_eq!(
            parametric.value(space.dimension_index("affinity").unwrap()),
            Some(&crate::dimension::DimValue::Top)
        );
    }

    #[test]
    fn slot_type_to_parametric_slot_type_converts_all_fields() {
        let space = crate::dimension::StandardDimensions::vca();
        let slot_type = SlotType {
            family: Family::Data,
            kind: Kind::PatternMatch,
            layer: Layer::N(3),
            affinity: Affinity::Lax,
            lower: 2,
            upper: UpperBound::Finite(10),
            id: TypeId(42),
            meta: TypeMeta::None,
        };
        let parametric = slot_type
            .to_parametric_slot_type(&space)
            .expect("conversion should succeed");
        assert_eq!(
            parametric.value(space.dimension_index("family").unwrap()),
            Some(&crate::dimension::DimValue::Named("Data".to_string()))
        );
        assert_eq!(
            parametric.value(space.dimension_index("kind").unwrap()),
            Some(&crate::dimension::DimValue::Named(
                "PatternMatch".to_string()
            ))
        );
        assert_eq!(
            parametric.value(space.dimension_index("layer").unwrap()),
            Some(&crate::dimension::DimValue::Num(3))
        );
        assert_eq!(
            parametric.value(space.dimension_index("affinity").unwrap()),
            Some(&crate::dimension::DimValue::Named("Lax".to_string()))
        );
        assert_eq!(
            parametric.value(space.dimension_index("lower").unwrap()),
            Some(&crate::dimension::DimValue::Num(2))
        );
        assert_eq!(
            parametric.value(space.dimension_index("upper").unwrap()),
            Some(&crate::dimension::DimValue::Num(10))
        );
        assert_eq!(
            parametric.value(space.dimension_index("id").unwrap()),
            Some(&crate::dimension::DimValue::Num(42))
        );
    }

    #[test]
    fn slot_type_to_parametric_slot_type_infinite_upper() {
        let space = crate::dimension::StandardDimensions::vca();
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
        let parametric = slot_type
            .to_parametric_slot_type(&space)
            .expect("conversion should succeed");
        assert_eq!(
            parametric.value(space.dimension_index("upper").unwrap()),
            Some(&crate::dimension::DimValue::Named("Infinite".to_string()))
        );
    }

    #[test]
    fn typemeta_none_is_default() {
        let meta = TypeMeta::None;
        assert_eq!(meta, TypeMeta::None);
    }

    #[test]
    fn typemeta_patternmatch_stores_patterns_correctly() {
        let pattern_source = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let pattern_target = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Lax,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let meta = TypeMeta::PatternMatch {
            pattern_source: Box::new(pattern_source.clone()),
            pattern_target: Box::new(pattern_target.clone()),
        };
        match meta {
            TypeMeta::PatternMatch {
                pattern_source: src,
                pattern_target: tgt,
            } => {
                assert_eq!(*src, pattern_source);
                assert_eq!(*tgt, pattern_target);
            }
            _ => panic!("expected PatternMatch variant"),
        }
    }

    #[test]
    fn typemeta_eq_stores_position_and_pairs_correctly() {
        use crate::relation::PosIndex;
        use std::collections::HashSet;
        let i_eq: PosIndex = 0;
        let mut id_pairs = HashSet::new();
        id_pairs.insert((1, 2));
        id_pairs.insert((3, 4));
        let meta = TypeMeta::Eq { i_eq, id_pairs };
        match meta {
            TypeMeta::Eq {
                i_eq: pos,
                id_pairs: pairs,
            } => {
                assert_eq!(pos, 0);
                assert_eq!(pairs.len(), 2);
                assert!(pairs.contains(&(1, 2)));
                assert!(pairs.contains(&(3, 4)));
            }
            _ => panic!("expected Eq variant"),
        }
    }

    #[test]
    fn typemeta_implements_clone() {
        let meta1 = TypeMeta::None;
        let meta2 = meta1.clone();
        assert_eq!(meta1, meta2);
    }

    #[test]
    fn typemeta_implements_debug() {
        let meta = TypeMeta::None;
        let debug_str = format!("{:?}", meta);
        assert!(debug_str.contains("None"));
    }

    #[test]
    fn typemeta_implements_partial_eq() {
        let meta1 = TypeMeta::None;
        let meta2 = TypeMeta::None;
        assert_eq!(meta1, meta2);
    }

    #[test]
    fn typemeta_implements_eq() {
        let meta1 = TypeMeta::None;
        let meta2 = TypeMeta::None;
        assert_eq!(meta1, meta2);
    }

    #[allow(deprecated)]
    #[test]
    fn ltype_with_meta_none_works_for_backward_compatibility() {
        let ltype = LType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        assert_eq!(ltype.meta, TypeMeta::None);
        assert!(type_matches(&ltype, &ltype));
    }

    #[allow(deprecated)]
    #[test]
    fn ltype_with_meta_patternmatch_stores_metadata() {
        let pattern_source = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let pattern_target = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Lax,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let ltype = LType {
            family: Family::Rule,
            kind: Kind::PatternMatch,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            meta: TypeMeta::PatternMatch {
                pattern_source: Box::new(pattern_source.clone()),
                pattern_target: Box::new(pattern_target.clone()),
            },
        };
        match ltype.meta {
            TypeMeta::PatternMatch {
                pattern_source: src,
                pattern_target: tgt,
            } => {
                assert_eq!(*src, pattern_source);
                assert_eq!(*tgt, pattern_target);
            }
            _ => panic!("expected PatternMatch variant"),
        }
    }

    #[allow(deprecated)]
    #[test]
    fn ltype_same_fields_different_meta_not_equal() {
        let ltype1 = LType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        let pattern_source = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let pattern_target = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Lax,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let ltype2 = LType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            meta: TypeMeta::PatternMatch {
                pattern_source: Box::new(pattern_source),
                pattern_target: Box::new(pattern_target),
            },
        };
        assert_ne!(ltype1, ltype2);
    }

    #[allow(deprecated)]
    #[test]
    fn type_matches_ignores_meta() {
        let pattern = LType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            meta: TypeMeta::None,
        };
        let pattern_source = SlotType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            lower: 0,
            upper: UpperBound::Finite(10),
            id: TypeId(1),
            meta: TypeMeta::None,
        };
        let pattern_target = SlotType {
            family: Family::Rule,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Lax,
            lower: 0,
            upper: UpperBound::Infinite,
            id: TypeId(2),
            meta: TypeMeta::None,
        };
        let actual = LType {
            family: Family::Data,
            kind: Kind::Any,
            layer: Layer::N(0),
            affinity: Affinity::Strict,
            meta: TypeMeta::PatternMatch {
                pattern_source: Box::new(pattern_source),
                pattern_target: Box::new(pattern_target),
            },
        };
        assert!(type_matches(&pattern, &actual));
    }
}

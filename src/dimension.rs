/// A value in a type dimension: Top (wildcard), Bot (empty), Named, or Num.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum DimValue {
    Top,
    Bot,
    Named(String),
    Num(u64),
}

/// A named dimension in the parametric type space with a finite domain.
#[derive(Clone, Debug)]
pub struct Dimension {
    pub name: String,
    pub domain: Vec<DimValue>,
}

impl Dimension {
    pub fn new(name: String, domain: Vec<DimValue>) -> Self {
        Dimension { name, domain }
    }
}

/// The product type space `T = ∏(d ∈ D) T_d`.
#[derive(Clone, Debug)]
pub struct TypeSpace {
    pub dimensions: Vec<Dimension>,
}

impl TypeSpace {
    pub fn new(dimensions: Vec<Dimension>) -> Self {
        TypeSpace { dimensions }
    }

    pub fn dimension_count(&self) -> usize {
        self.dimensions.len()
    }

    pub fn dimension_index(&self, name: &str) -> Option<usize> {
        self.dimensions.iter().position(|d| d.name == name)
    }
}

/// A type expressed as a vector of dimension values, supporting Top/Bot matching.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ParametricSlotType {
    values: Vec<DimValue>,
}

impl ParametricSlotType {
    pub fn new(values: Vec<DimValue>) -> Self {
        ParametricSlotType { values }
    }

    pub fn matches(&self, pattern: &ParametricSlotType) -> bool {
        if self.values.len() != pattern.values.len() {
            return false;
        }
        self.values
            .iter()
            .zip(&pattern.values)
            .all(|(actual, pat)| match pat {
                DimValue::Top => true,
                DimValue::Bot => false,
                _ => actual == pat,
            })
    }

    pub fn value(&self, index: usize) -> Option<&DimValue> {
        self.values.get(index)
    }

    pub fn values(&self) -> &[DimValue] {
        &self.values
    }
}

pub struct StandardDimensions;

impl StandardDimensions {
    pub fn vca() -> TypeSpace {
        let family_dim = Dimension::new(
            "family".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Named("Rule".to_string()),
                DimValue::Named("Data".to_string()),
            ],
        );

        let kind_dim = Dimension::new(
            "kind".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Named("Any".to_string()),
                DimValue::Named("None".to_string()),
                DimValue::Named("PatternMatch".to_string()),
                DimValue::Named("Eq".to_string()),
            ],
        );

        let layer_dim = Dimension::new(
            "layer".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Num(0),
                DimValue::Num(1),
                DimValue::Num(2),
                DimValue::Num(3),
                DimValue::Num(4),
                DimValue::Num(5),
            ],
        );

        let affinity_dim = Dimension::new(
            "affinity".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Named("Strict".to_string()),
                DimValue::Named("Lax".to_string()),
            ],
        );

        let lower_dim = Dimension::new(
            "lower".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Num(0),
                DimValue::Num(1),
                DimValue::Num(2),
                DimValue::Num(3),
                DimValue::Num(4),
                DimValue::Num(5),
            ],
        );

        let upper_dim = Dimension::new(
            "upper".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Num(0),
                DimValue::Num(1),
                DimValue::Num(2),
                DimValue::Num(3),
                DimValue::Num(4),
                DimValue::Num(5),
                DimValue::Named("Infinite".to_string()),
            ],
        );

        let id_dim = Dimension::new(
            "id".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Named("uuid".to_string()),
            ],
        );

        let meta_dim = Dimension::new(
            "meta".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Named("pattern".to_string()),
            ],
        );

        TypeSpace::new(vec![
            family_dim,
            kind_dim,
            layer_dim,
            affinity_dim,
            lower_dim,
            upper_dim,
            id_dim,
            meta_dim,
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::rstest;

    #[test]
    fn dim_value_top_equals_top() {
        assert_eq!(DimValue::Top, DimValue::Top);
    }

    #[test]
    fn dim_value_named_equals_same_name() {
        assert_eq!(
            DimValue::Named("Rule".to_string()),
            DimValue::Named("Rule".to_string())
        );
    }

    #[test]
    fn dim_value_num_equals_same_num() {
        assert_eq!(DimValue::Num(42), DimValue::Num(42));
    }

    #[test]
    fn dimension_new_creates_with_name_and_domain() {
        let dim = Dimension::new(
            "test".to_string(),
            vec![
                DimValue::Top,
                DimValue::Bot,
                DimValue::Named("x".to_string()),
            ],
        );
        assert_eq!(dim.name, "test");
        assert_eq!(dim.domain.len(), 3);
    }

    #[test]
    fn type_space_new_creates_with_dimensions() {
        let dim1 = Dimension::new("d1".to_string(), vec![DimValue::Top]);
        let dim2 = Dimension::new("d2".to_string(), vec![DimValue::Bot]);
        let space = TypeSpace::new(vec![dim1, dim2]);
        assert_eq!(space.dimension_count(), 2);
    }

    #[test]
    fn type_space_dimension_index_finds_by_name() {
        let dim1 = Dimension::new("family".to_string(), vec![DimValue::Top]);
        let dim2 = Dimension::new("kind".to_string(), vec![DimValue::Top]);
        let space = TypeSpace::new(vec![dim1, dim2]);
        assert_eq!(space.dimension_index("family"), Some(0));
        assert_eq!(space.dimension_index("kind"), Some(1));
        assert_eq!(space.dimension_index("missing"), None);
    }

    #[test]
    fn parametric_slot_type_new_creates_with_values() {
        let values = vec![
            DimValue::Top,
            DimValue::Bot,
            DimValue::Named("x".to_string()),
        ];
        let slot_type = ParametricSlotType::new(values.clone());
        assert_eq!(slot_type.values(), values.as_slice());
    }

    #[rstest]
    #[case::top_matches_any(
        vec![DimValue::Top],
        vec![DimValue::Named("Rule".to_string())],
        true
    )]
    #[case::exact_match(
        vec![DimValue::Named("Rule".to_string())],
        vec![DimValue::Named("Rule".to_string())],
        true
    )]
    #[case::mismatch(
        vec![DimValue::Named("Rule".to_string())],
        vec![DimValue::Named("Data".to_string())],
        false
    )]
    #[case::bot_matches_nothing(
        vec![DimValue::Bot],
        vec![DimValue::Named("Rule".to_string())],
        false
    )]
    #[case::bot_not_self(
        vec![DimValue::Bot],
        vec![DimValue::Bot],
        false
    )]
    fn parametric_slot_type_matches_cases(
        #[case] pattern_values: Vec<DimValue>,
        #[case] actual_values: Vec<DimValue>,
        #[case] expected: bool,
    ) {
        let pattern = ParametricSlotType::new(pattern_values);
        let actual = ParametricSlotType::new(actual_values);
        assert_eq!(actual.matches(&pattern), expected);
    }

    #[test]
    fn parametric_slot_type_matches_different_lengths_returns_false() {
        let pattern = ParametricSlotType::new(vec![DimValue::Top, DimValue::Top]);
        let actual = ParametricSlotType::new(vec![DimValue::Top]);
        assert!(!actual.matches(&pattern));
    }

    #[test]
    fn parametric_slot_type_matches_multi_dimensional() {
        let pattern = ParametricSlotType::new(vec![
            DimValue::Top,
            DimValue::Named("Any".to_string()),
            DimValue::Num(5),
            DimValue::Top,
        ]);
        let actual1 = ParametricSlotType::new(vec![
            DimValue::Named("Rule".to_string()),
            DimValue::Named("Any".to_string()),
            DimValue::Num(5),
            DimValue::Named("Strict".to_string()),
        ]);
        let actual2 = ParametricSlotType::new(vec![
            DimValue::Named("Data".to_string()),
            DimValue::Named("Any".to_string()),
            DimValue::Num(5),
            DimValue::Named("Lax".to_string()),
        ]);
        assert!(actual1.matches(&pattern));
        assert!(actual2.matches(&pattern));
    }

    #[test]
    fn standard_dimensions_vca_creates_eight_dimensions() {
        let space = StandardDimensions::vca();
        assert_eq!(space.dimension_count(), 8);
        assert_eq!(space.dimension_index("family"), Some(0));
        assert_eq!(space.dimension_index("kind"), Some(1));
        assert_eq!(space.dimension_index("layer"), Some(2));
        assert_eq!(space.dimension_index("affinity"), Some(3));
        assert_eq!(space.dimension_index("lower"), Some(4));
        assert_eq!(space.dimension_index("upper"), Some(5));
        assert_eq!(space.dimension_index("id"), Some(6));
        assert_eq!(space.dimension_index("meta"), Some(7));
    }

    #[test]
    fn standard_dimensions_vca_family_contains_rule_and_data() {
        let space = StandardDimensions::vca();
        let family_dim = &space.dimensions[0];
        assert!(family_dim.domain.contains(&DimValue::Top));
        assert!(family_dim.domain.contains(&DimValue::Bot));
        assert!(
            family_dim
                .domain
                .contains(&DimValue::Named("Rule".to_string()))
        );
        assert!(
            family_dim
                .domain
                .contains(&DimValue::Named("Data".to_string()))
        );
    }

    #[test]
    fn standard_dimensions_vca_kind_contains_all_variants() {
        let space = StandardDimensions::vca();
        let kind_dim = &space.dimensions[1];
        assert!(kind_dim.domain.contains(&DimValue::Top));
        assert!(kind_dim.domain.contains(&DimValue::Bot));
        assert!(
            kind_dim
                .domain
                .contains(&DimValue::Named("Any".to_string()))
        );
        assert!(
            kind_dim
                .domain
                .contains(&DimValue::Named("None".to_string()))
        );
        assert!(
            kind_dim
                .domain
                .contains(&DimValue::Named("PatternMatch".to_string()))
        );
        assert!(kind_dim.domain.contains(&DimValue::Named("Eq".to_string())));
    }
}

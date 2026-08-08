//! Type environments: the typing context a formula is checked against.
//!
//! An environment maps free-identifier names to their [`Type`]s. It is
//! built mutably ([`TypeEnvironmentBuilder`]), then sealed into an
//! immutable snapshot ([`SealedTypeEnvironment`]) that is cheap to
//! clone and share; type-checking only ever reads sealed environments.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::types::Type;

/// A mutable type environment under construction.
#[derive(Debug, Default, Clone)]
pub struct TypeEnvironmentBuilder {
    map: BTreeMap<String, Type>,
}

impl TypeEnvironmentBuilder {
    /// An empty environment.
    pub fn new() -> Self {
        Self::default()
    }

    /// Binds `name` to `ty`, replacing any previous binding.
    pub fn insert(&mut self, name: impl Into<String>, ty: Type) {
        self.map.insert(name.into(), ty);
    }

    /// Declares a carrier set: binds `name` to `ℙ(name)`.
    pub fn add_given_set(&mut self, name: &str) {
        self.insert(name, Type::carrier_set_type(name));
    }

    /// The type bound to `name`, if any.
    pub fn get(&self, name: &str) -> Option<&Type> {
        self.map.get(name)
    }

    /// Whether `name` is bound.
    pub fn contains(&self, name: &str) -> bool {
        self.map.contains_key(name)
    }

    /// Iterates over the bindings in name order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &Type)> {
        self.map.iter().map(|(name, ty)| (name.as_str(), ty))
    }

    /// Seals the current bindings into an immutable snapshot. The
    /// builder remains usable; later changes do not affect the snapshot.
    pub fn make_snapshot(&self) -> SealedTypeEnvironment {
        SealedTypeEnvironment(Arc::new(self.map.clone()))
    }
}

/// An immutable type-environment snapshot.
///
/// Cloning is O(1); the bindings are shared.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct SealedTypeEnvironment(Arc<BTreeMap<String, Type>>);

impl SealedTypeEnvironment {
    /// The type bound to `name`, if any.
    pub fn get(&self, name: &str) -> Option<&Type> {
        self.0.get(name)
    }

    /// Whether `name` is bound.
    pub fn contains(&self, name: &str) -> bool {
        self.0.contains_key(name)
    }

    /// Iterates over the bindings in name order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &Type)> {
        self.0.iter().map(|(name, ty)| (name.as_str(), ty))
    }

    /// Number of bindings.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Whether the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Copies the bindings back into a builder, e.g. to derive an inner
    /// scope from a sealed machine environment.
    pub fn to_builder(&self) -> TypeEnvironmentBuilder {
        TypeEnvironmentBuilder {
            map: (*self.0).clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn snapshot_is_isolated_from_later_changes() {
        let mut builder = TypeEnvironmentBuilder::new();
        builder.insert("x", Type::Int);
        let sealed = builder.make_snapshot();
        builder.insert("y", Type::Bool);
        builder.insert("x", Type::Bool);

        assert_eq!(sealed.get("x"), Some(&Type::Int));
        assert!(!sealed.contains("y"));
        assert_eq!(sealed.len(), 1);
        assert_eq!(builder.get("x"), Some(&Type::Bool));
    }

    #[test]
    fn given_set_binds_to_its_own_powerset() {
        let mut builder = TypeEnvironmentBuilder::new();
        builder.add_given_set("USERS");
        assert_eq!(builder.get("USERS"), Some(&Type::pow(Type::given("USERS"))));
    }

    #[test]
    fn iteration_is_name_ordered() {
        let mut builder = TypeEnvironmentBuilder::new();
        builder.insert("b", Type::Int);
        builder.insert("a", Type::Bool);
        builder.insert("c", Type::Int);
        let sealed = builder.make_snapshot();
        let names: Vec<&str> = sealed.iter().map(|(n, _)| n).collect();
        assert_eq!(names, ["a", "b", "c"]);
    }

    #[test]
    fn round_trip_through_builder() {
        let mut builder = TypeEnvironmentBuilder::new();
        builder.insert("x", Type::Int);
        let sealed = builder.make_snapshot();

        let mut inner = sealed.to_builder();
        inner.insert("p", Type::Bool);
        assert_eq!(inner.get("x"), Some(&Type::Int));
        assert_eq!(inner.get("p"), Some(&Type::Bool));
        // The original snapshot is unaffected by the derived scope.
        assert!(!sealed.contains("p"));
    }
}

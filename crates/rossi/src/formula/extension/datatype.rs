//! Inductive datatypes as extension bundles.
//!
//! A datatype declaration like `List(T) ::= nil ∥ cons(head: T,
//! tail: List(T))` yields one type-constructor extension (`List`, whose
//! instances appear in [`Type::Parametric`]), one constructor extension
//! per variant, and one destructor extension per named argument. All of
//! them are ordinary operator extensions; a factory carrying them
//! accepts the datatype's formulas.
//!
//! Argument types are *specifications* over the declaration: a given
//! set named like a type parameter stands for that parameter, and the
//! placeholder returned by [`DatatypeBuilder::self_type`] stands for
//! the datatype under construction (recursion). Both are instantiated
//! at each use site.

use std::sync::{Arc, OnceLock};

use super::super::decl::BoundIdentDecl;
use super::super::expression::Expression;
use super::super::factory::{self, FormulaFactory};
use super::super::predicate::Predicate;
use super::super::tag::{QuantPredOp, RelationalOp, Tag};
use super::super::typecheck::{TcType, TypeCheckMediator};
use super::super::types::Type;
use super::super::wd::WdMediator;
use super::{ExpressionExtension, ExtendedRef, Extension, ExtensionKind, FormulaExtension};

/// A malformed datatype declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DatatypeError {
    /// A datatype needs at least one constructor.
    NoConstructors,
    /// Two operators of the declaration share a name.
    DuplicateName(String),
}

/// The declaration under construction.
pub struct DatatypeBuilder {
    name: String,
    params: Vec<String>,
    constructors: Vec<ConstructorSpec>,
}

struct ConstructorSpec {
    name: String,
    /// Arguments: optional destructor name, and the argument's type
    /// specification.
    args: Vec<(Option<String>, Type)>,
}

impl DatatypeBuilder {
    /// Starts a declaration of `name` over the given type parameters.
    pub fn new(name: impl Into<String>, params: &[&str]) -> DatatypeBuilder {
        DatatypeBuilder {
            name: name.into(),
            params: params.iter().map(|p| p.to_string()).collect(),
            constructors: Vec::new(),
        }
    }

    /// The specification placeholder for the datatype itself, for
    /// recursive arguments.
    pub fn self_type(&self) -> Type {
        Type::Parametric {
            tag: super::super::tag::NO_TAG,
            symbol: self.name.clone(),
            params: self.params.iter().map(Type::given).collect(),
        }
    }

    /// Adds a constructor.
    pub fn constructor(&mut self, name: impl Into<String>) -> &mut DatatypeBuilder {
        self.constructors.push(ConstructorSpec {
            name: name.into(),
            args: Vec::new(),
        });
        self
    }

    /// Adds an argument to the last constructor; a named argument gets
    /// a destructor.
    #[track_caller]
    pub fn arg(&mut self, destructor: Option<&str>, ty: Type) -> &mut DatatypeBuilder {
        let spec = self
            .constructors
            .last_mut()
            .expect("add a constructor before its arguments");
        spec.args.push((destructor.map(str::to_string), ty));
        self
    }

    /// Validates the declaration and produces the extension bundle.
    pub fn finalize(self) -> Result<Datatype, DatatypeError> {
        if self.constructors.is_empty() {
            return Err(DatatypeError::NoConstructors);
        }
        let mut names: Vec<&str> = vec![&self.name];
        for ctor in &self.constructors {
            names.push(&ctor.name);
            for (destructor, _) in &ctor.args {
                if let Some(name) = destructor {
                    names.push(name);
                }
            }
        }
        names.sort_unstable();
        if let Some(pair) = names.windows(2).find(|pair| pair[0] == pair[1]) {
            return Err(DatatypeError::DuplicateName(pair[0].to_string()));
        }

        let core = Arc::new(DatatypeCore {
            name: self.name,
            params: self.params,
            tag: OnceLock::new(),
            single_constructor: self.constructors.len() == 1,
        });
        let type_constructor: Arc<TypeConstructorExt> =
            Arc::new(TypeConstructorExt { core: core.clone() });
        // The type constructor's permanent tag is what parametric
        // instances carry, so it is allocated right away.
        let as_extension = Extension::Expr(type_constructor.clone());
        let tag = factory::register_extension_tag(&as_extension);
        core.tag.set(tag).expect("tag set once");

        let mut constructors: Vec<Arc<ConstructorExt>> = Vec::new();
        let mut destructors: Vec<Arc<DestructorExt>> = Vec::new();
        for spec in self.constructors {
            let ctor = Arc::new(ConstructorExt {
                core: core.clone(),
                name: spec.name,
                args: spec.args,
            });
            for (destructor, ty) in &ctor.args {
                if let Some(name) = destructor {
                    destructors.push(Arc::new(DestructorExt {
                        core: core.clone(),
                        name: name.clone(),
                        constructor: ctor.clone(),
                        arg_ty: ty.clone(),
                    }));
                }
            }
            constructors.push(ctor);
        }
        Ok(Datatype {
            core,
            type_constructor,
            constructors,
            destructors,
        })
    }
}

/// A finalized datatype: the bundle of extensions it declares.
///
/// Debug output shows the declaration's operator names only.
pub struct Datatype {
    core: Arc<DatatypeCore>,
    type_constructor: Arc<TypeConstructorExt>,
    constructors: Vec<Arc<ConstructorExt>>,
    destructors: Vec<Arc<DestructorExt>>,
}

impl Datatype {
    /// The datatype's name.
    pub fn name(&self) -> &str {
        &self.core.name
    }

    /// The type constructor's permanent tag: what parametric instances
    /// carry.
    pub fn tag(&self) -> Tag {
        self.core.tag()
    }

    /// The type-constructor extension.
    pub fn type_constructor(&self) -> Arc<dyn ExpressionExtension> {
        self.type_constructor.clone()
    }

    /// The constructor extension named `name`, if any.
    pub fn constructor(&self, name: &str) -> Option<Arc<dyn ExpressionExtension>> {
        self.constructors
            .iter()
            .find(|c| c.name == name)
            .map(|c| c.clone() as Arc<dyn ExpressionExtension>)
    }

    /// The destructor extension named `name`, if any.
    pub fn destructor(&self, name: &str) -> Option<Arc<dyn ExpressionExtension>> {
        self.destructors
            .iter()
            .find(|d| d.name == name)
            .map(|d| d.clone() as Arc<dyn ExpressionExtension>)
    }

    /// Every extension the datatype declares.
    pub fn extensions(&self) -> Vec<Extension> {
        let mut extensions: Vec<Extension> = vec![Extension::Expr(self.type_constructor.clone())];
        extensions.extend(
            self.constructors
                .iter()
                .map(|c| Extension::Expr(c.clone() as Arc<dyn ExpressionExtension>)),
        );
        extensions.extend(
            self.destructors
                .iter()
                .map(|d| Extension::Expr(d.clone() as Arc<dyn ExpressionExtension>)),
        );
        extensions
    }

    fn debug_names(&self) -> Vec<&str> {
        let mut names = vec![self.core.name.as_str()];
        names.extend(self.constructors.iter().map(|c| c.name.as_str()));
        names.extend(self.destructors.iter().map(|d| d.name.as_str()));
        names
    }

    /// The interned factory supporting this datatype.
    pub fn factory(&self) -> FormulaFactory {
        FormulaFactory::with_extensions(self.extensions())
            .expect("a finalized datatype has distinct operator names")
    }
}

impl std::fmt::Debug for Datatype {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Datatype")
            .field(&self.debug_names())
            .finish()
    }
}

struct DatatypeCore {
    name: String,
    params: Vec<String>,
    tag: OnceLock<Tag>,
    single_constructor: bool,
}

impl DatatypeCore {
    fn tag(&self) -> Tag {
        *self.tag.get().expect("allocated at finalization")
    }

    fn param_index(&self, name: &str) -> Option<usize> {
        self.params.iter().position(|p| p == name)
    }

    /// The datatype's instance type over concrete parameters.
    fn instance(&self, params: Vec<Type>) -> Type {
        Type::Parametric {
            tag: self.tag(),
            symbol: self.name.clone(),
            params,
        }
    }

    /// Instantiates a specification with concrete parameter types.
    fn instantiate(&self, spec: &Type, params: &[Type]) -> Type {
        match spec {
            Type::Given(name) => match self.param_index(name) {
                Some(index) => params[index].clone(),
                None => spec.clone(),
            },
            Type::Parametric {
                tag: super::super::tag::NO_TAG,
                symbol,
                ..
            } if *symbol == self.name => self.instance(params.to_vec()),
            Type::Pow(inner) => Type::pow(self.instantiate(inner, params)),
            Type::Prod(left, right) => Type::prod(
                self.instantiate(left, params),
                self.instantiate(right, params),
            ),
            _ => spec.clone(),
        }
    }

    /// Instantiates a specification with solver parameter handles.
    fn instantiate_tc(
        &self,
        spec: &Type,
        params: &[TcType],
        mediator: &mut TypeCheckMediator<'_, '_>,
    ) -> TcType {
        match spec {
            Type::Given(name) => match self.param_index(name) {
                Some(index) => params[index],
                None => mediator.from_type(spec),
            },
            Type::Parametric {
                tag: super::super::tag::NO_TAG,
                symbol,
                ..
            } if *symbol == self.name => {
                mediator.parametric(self.tag(), &self.name, params.to_vec())
            }
            Type::Pow(inner) => {
                let inner = self.instantiate_tc(inner, params, mediator);
                mediator.pow(inner)
            }
            Type::Prod(left, right) => {
                let left = self.instantiate_tc(left, params, mediator);
                let right = self.instantiate_tc(right, params, mediator);
                mediator.prod(left, right)
            }
            _ => mediator.from_type(spec),
        }
    }

    /// Solves the parameter bindings that make `spec` equal `actual`.
    fn match_spec(&self, spec: &Type, actual: &Type, bindings: &mut [Option<Type>]) -> bool {
        match (spec, actual) {
            (Type::Given(name), _) => match self.param_index(name) {
                Some(index) => match &bindings[index] {
                    Some(bound) => bound == actual,
                    None => {
                        bindings[index] = Some(actual.clone());
                        true
                    }
                },
                None => spec == actual,
            },
            (
                Type::Parametric {
                    tag: super::super::tag::NO_TAG,
                    symbol,
                    ..
                },
                Type::Parametric {
                    tag: actual_tag,
                    params: actual_params,
                    ..
                },
            ) if *symbol == self.name => {
                *actual_tag == self.tag()
                    && actual_params.len() == self.params.len()
                    && self
                        .params
                        .clone()
                        .iter()
                        .zip(actual_params)
                        .all(|(param, actual)| {
                            self.match_spec(&Type::given(param.clone()), actual, bindings)
                        })
            }
            (Type::Pow(spec), Type::Pow(actual)) => self.match_spec(spec, actual, bindings),
            (Type::Prod(sl, sr), Type::Prod(al, ar)) => {
                self.match_spec(sl, al, bindings) && self.match_spec(sr, ar, bindings)
            }
            _ => spec == actual,
        }
    }
}

/// `List` — instances of this operator denote the datatype's sets.
struct TypeConstructorExt {
    core: Arc<DatatypeCore>,
}

impl FormulaExtension for TypeConstructorExt {
    fn symbol(&self) -> &str {
        &self.core.name
    }
    fn id(&self) -> &str {
        &self.core.name
    }
    fn group_id(&self) -> &str {
        "datatype"
    }
    fn kind(&self) -> ExtensionKind {
        ExtensionKind::prefix_expression(self.core.params.len())
    }
    fn conjoin_children_wd(&self) -> bool {
        true
    }
    fn wd_predicate(&self, _formula: ExtendedRef<'_>, wd: &WdMediator<'_>) -> Predicate {
        wd.true_wd()
    }
}

impl ExpressionExtension for TypeConstructorExt {
    fn synthesize_type(&self, exprs: &[Expression], _: &[Predicate]) -> Option<Type> {
        let params: Option<Vec<Type>> = exprs
            .iter()
            .map(|e| e.ty().and_then(Type::base_type).cloned())
            .collect();
        Some(Type::pow(self.core.instance(params?)))
    }

    fn verify_type(&self, proposed: &Type, _: &[Expression], _: &[Predicate]) -> bool {
        matches!(
            proposed.base_type(),
            Some(Type::Parametric { tag, params, .. })
                if *tag == self.core.tag() && params.len() == self.core.params.len()
        )
    }

    fn type_check(&self, mediator: &mut TypeCheckMediator<'_, '_>, exprs: &[TcType]) -> TcType {
        let params: Vec<TcType> = exprs
            .iter()
            .map(|child| {
                let param = mediator.fresh();
                let set = mediator.pow(param);
                mediator.same_type(*child, set);
                param
            })
            .collect();
        let instance = mediator.parametric(self.core.tag(), &self.core.name, params);
        mediator.pow(instance)
    }

    fn is_a_type_constructor(&self) -> bool {
        true
    }
}

/// `cons(…)` — builds a datatype value.
struct ConstructorExt {
    core: Arc<DatatypeCore>,
    name: String,
    args: Vec<(Option<String>, Type)>,
}

impl FormulaExtension for ConstructorExt {
    fn symbol(&self) -> &str {
        &self.name
    }
    fn id(&self) -> &str {
        &self.name
    }
    fn group_id(&self) -> &str {
        "datatype"
    }
    fn kind(&self) -> ExtensionKind {
        ExtensionKind::prefix_expression(self.args.len())
    }
    fn conjoin_children_wd(&self) -> bool {
        true
    }
    fn wd_predicate(&self, _formula: ExtendedRef<'_>, wd: &WdMediator<'_>) -> Predicate {
        wd.true_wd()
    }
}

impl ConstructorExt {
    /// Binds the datatype parameters from the actual argument types.
    fn solve_params(&self, exprs: &[Expression]) -> Option<Vec<Type>> {
        let mut bindings: Vec<Option<Type>> = vec![None; self.core.params.len()];
        for ((_, spec), child) in self.args.iter().zip(exprs) {
            if !self.core.match_spec(spec, child.ty()?, &mut bindings) {
                return None;
            }
        }
        bindings.into_iter().collect()
    }
}

impl ExpressionExtension for ConstructorExt {
    fn synthesize_type(&self, exprs: &[Expression], _: &[Predicate]) -> Option<Type> {
        Some(self.core.instance(self.solve_params(exprs)?))
    }

    fn verify_type(&self, proposed: &Type, exprs: &[Expression], _: &[Predicate]) -> bool {
        match proposed {
            Type::Parametric { tag, params, .. }
                if *tag == self.core.tag() && params.len() == self.core.params.len() =>
            {
                match self.solve_params(exprs) {
                    Some(solved) => solved == *params,
                    // Untyped children: accept any instance shape.
                    None => true,
                }
            }
            _ => false,
        }
    }

    fn type_check(&self, mediator: &mut TypeCheckMediator<'_, '_>, exprs: &[TcType]) -> TcType {
        let params: Vec<TcType> = (0..self.core.params.len())
            .map(|_| mediator.fresh())
            .collect();
        for ((_, spec), child) in self.args.iter().zip(exprs) {
            let expected = self.core.instantiate_tc(spec, &params, mediator);
            mediator.same_type(*child, expected);
        }
        mediator.parametric(self.core.tag(), &self.core.name, params)
    }
}

/// `head(…)` — projects one constructor argument.
struct DestructorExt {
    core: Arc<DatatypeCore>,
    name: String,
    constructor: Arc<ConstructorExt>,
    /// The projected argument's type specification.
    arg_ty: Type,
}

impl FormulaExtension for DestructorExt {
    fn symbol(&self) -> &str {
        &self.name
    }
    fn id(&self) -> &str {
        &self.name
    }
    fn group_id(&self) -> &str {
        "datatype"
    }
    fn kind(&self) -> ExtensionKind {
        ExtensionKind::prefix_expression(1)
    }
    fn conjoin_children_wd(&self) -> bool {
        true
    }

    /// A destructor denotes only on values of its constructor:
    /// `∃ args · value = cons(args)`. With a single constructor every
    /// value qualifies.
    fn wd_predicate(&self, formula: ExtendedRef<'_>, wd: &WdMediator<'_>) -> Predicate {
        if self.core.single_constructor {
            return wd.true_wd();
        }
        let value = &formula.exprs[0];
        let ff = wd.factory();
        let Some(Type::Parametric { params, .. }) = value.ty() else {
            return wd.true_wd();
        };
        let args = &self.constructor.args;
        let arg_tys: Vec<Type> = args
            .iter()
            .map(|(_, spec)| self.core.instantiate(spec, params))
            .collect();
        let n = args.len() as u32;
        let decls: Vec<BoundIdentDecl> = args
            .iter()
            .zip(&arg_tys)
            .enumerate()
            .map(|(i, ((destructor, _), ty))| {
                let hint = match destructor {
                    Some(name) => format!("{name}{i}"),
                    None => format!("p{i}"),
                };
                ff.bound_ident_decl(hint, None, None, Some(ty.clone()))
            })
            .collect();
        let bound_args: Vec<Expression> = arg_tys
            .iter()
            .enumerate()
            .map(|(i, ty)| ff.bound_identifier(n - 1 - i as u32, None, Some(ty.clone())))
            .collect();
        let built = ff
            .extended_expression(
                &(self.constructor.clone() as Arc<dyn ExpressionExtension>),
                bound_args,
                vec![],
                None,
                Some(value.ty().expect("typed value").clone()),
            )
            .expect("constructor arguments fit by construction");
        let equal = ff.relational_predicate(
            RelationalOp::Equal,
            value.shift_bound_identifiers(n as i32),
            built,
            None,
        );
        ff.quantified_predicate(QuantPredOp::Exists, decls, equal, None)
    }
}

impl ExpressionExtension for DestructorExt {
    fn synthesize_type(&self, exprs: &[Expression], _: &[Predicate]) -> Option<Type> {
        match exprs[0].ty()? {
            Type::Parametric { tag, params, .. } if *tag == self.core.tag() => {
                Some(self.core.instantiate(&self.arg_ty, params))
            }
            _ => None,
        }
    }

    fn verify_type(&self, proposed: &Type, exprs: &[Expression], preds: &[Predicate]) -> bool {
        match self.synthesize_type(exprs, preds) {
            Some(ty) => ty == *proposed,
            None => true,
        }
    }

    fn type_check(&self, mediator: &mut TypeCheckMediator<'_, '_>, exprs: &[TcType]) -> TcType {
        let params: Vec<TcType> = (0..self.core.params.len())
            .map(|_| mediator.fresh())
            .collect();
        let instance = mediator.parametric(self.core.tag(), &self.core.name, params.clone());
        mediator.same_type(exprs[0], instance);
        self.core.instantiate_tc(&self.arg_ty, &params, mediator)
    }
}

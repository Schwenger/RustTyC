use crate::types::{ChildConstraint, Children, ResolvedChildren};
use crate::{
    types::{Arity, Constructable, ContextSensitiveVariant, Partial, Preliminary, PreliminaryTypeTable, TypeTable},
    TcErr, TcKey,
};
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

#[derive(Debug, Clone)]
pub(crate) struct ConstraintGraph<T: ContextSensitiveVariant> {
    vertices: Vec<Vertex<T>>,
}

#[derive(Debug, Clone)]
enum Vertex<T: ContextSensitiveVariant> {
    /// Represents a former vertex that was unified with another one and not chosen to be the representative.
    Fwd { this: TcKey, repr: TcKey },
    /// Represents a full vertex.
    Repr(FullVertex<T>),
}

impl<T: ContextSensitiveVariant> Vertex<T> {
    fn this(&self) -> TcKey {
        match self {
            Vertex::Fwd { this, .. } => *this,
            Vertex::Repr(fv) => fv.this,
        }
    }

    /// Grants mutable access to the underlying full vertex.
    /// # Panics
    /// Panics if `self` is not a full vertex.
    fn mut_full(&mut self) -> &mut FullVertex<T> {
        match self {
            Vertex::Fwd { .. } => panic!("That's not a rep!!"),
            Vertex::Repr(vf) => vf,
        }
    }

    /// Grants immutable access to the underlying full vertex.
    /// # Panics
    /// Panics if `self` is not a full vertex.
    fn full(&self) -> &FullVertex<T> {
        match self {
            Vertex::Fwd { .. } => panic!("That's not a rep!!"),
            Vertex::Repr(vf) => vf,
        }
    }

    /// Returns the reference of the vertex representing this one.  Returns None if this vertex represents itself.
    fn get_repr_nontrans(&self) -> Option<TcKey> {
        match self {
            Vertex::Fwd { repr, .. } => Some(*repr),
            Vertex::Repr(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
struct FullVertex<T: ContextSensitiveVariant> {
    this: TcKey,
    ty: Type<T>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Type<V: ContextSensitiveVariant> {
    variant: V,
    children: Children,
    upper_bounds: HashSet<TcKey>,
}

type EquateObligation = Vec<(TcKey, TcKey)>;
type OptEquateObligation = Vec<Option<(TcKey, TcKey)>>;
impl<V: ContextSensitiveVariant> Type<V> {
    fn top() -> Self {
        Type { variant: V::top(), children: Children::Unknown, upper_bounds: HashSet::new() }
    }

    fn equal(this: &Self, that: &Self, ctx: &V::Context) -> bool {
        V::equal(&this.variant, &that.variant, ctx)
            && this.children == that.children
            && this.upper_bounds == that.upper_bounds
    }

    fn apply_child_constraint_checked(
        &mut self,
        this: TcKey,
        constraint: ChildConstraint,
        ctx: &V::Context,
    ) -> Result<(), TcErr<V>> {
        match (&self.variant.arity(ctx), constraint) {
            (Arity::None, ChildConstraint::Indexed(new_arity)) => {
                return Err(TcErr::ChildAccessOutOfBound(this, self.variant.clone(), new_arity))
            }
            (Arity::None, ChildConstraint::Named(new)) => {
                return Err(TcErr::FieldDoesNotExist(this, self.variant.clone(), new))
            }
            (Arity::None, ChildConstraint::Unconstrained) | (Arity::None, ChildConstraint::NoChildren) => {
                match &mut self.children {
                    Children::Unknown => self.children = Children::None,
                    Children::None => {}
                    Children::Indexed(_) | Children::Named(_) => {
                        unreachable!("Mismatch between arity type and children")
                    }
                }
            }
            (Arity::FixedIndexed(given_arity), ChildConstraint::Indexed(new_arity)) if new_arity > *given_arity => {
                return Err(TcErr::ChildAccessOutOfBound(this, self.variant.clone(), new_arity))
            }
            (Arity::FixedIndexed(given_arity), ChildConstraint::Indexed(_)) => match &mut self.children {
                Children::Unknown => self.children = Children::Indexed(vec![None; *given_arity]),
                Children::Indexed(children) => ConstraintGraph::<V>::fill_with(children, None, *given_arity),
                Children::Named(_) | Children::None => unreachable!("Mismatch between arity type and children"),
            },
            (Arity::Variable, ChildConstraint::Indexed(new_arity)) => match &mut self.children {
                Children::Unknown => self.children = Children::Indexed(vec![None; new_arity]),
                Children::Indexed(children) => ConstraintGraph::<V>::fill_with(children, None, new_arity),
                Children::Named(_) => {
                    return Err(TcErr::IndexedAccessOnNamedType(this, self.variant.clone(), new_arity));
                }
                Children::None => return Err(TcErr::ChildAccessOutOfBound(this, self.variant.clone(), new_arity)),
            },
            (Arity::FixedNamed(target), ChildConstraint::Named(new)) if !new.is_subset(target) => {
                return Err(TcErr::FieldDoesNotExist(
                    this,
                    self.variant.clone(),
                    new.difference(target).cloned().collect(),
                ))
            }
            (Arity::FixedNamed(target), ChildConstraint::Named(_)) => match &mut self.children {
                Children::Unknown => {
                    self.children = Children::Named(HashMap::from_iter(target.iter().map(|k| (k.clone(), None))))
                }
                Children::Named(names) => {
                    names.extend(target.difference(&names.keys().cloned().collect()).cloned().map(|k| (k, None)))
                }
                Children::Indexed(_) | Children::None => unreachable!("Mismatch between arity kind and children"),
            },
            (Arity::Variable, ChildConstraint::Named(names)) => match &mut self.children {
                Children::Unknown => {
                    self.children = Children::Named(HashMap::from_iter(names.into_iter().map(|k| (k, None))))
                }
                Children::Named(children) => {
                    let current: HashSet<String> = children.keys().cloned().collect();
                    children.extend(names.difference(&current).cloned().map(|k| (k, None)))
                }
                Children::Indexed(_) => {
                    return Err(TcErr::FieldAccessOnIndexedTyped(this, self.variant.clone(), names));
                }
                Children::None => return Err(TcErr::FieldDoesNotExist(this, self.variant.clone(), names)),
            },
            (Arity::FixedNamed(_), ChildConstraint::Indexed(idx)) => {
                return Err(TcErr::IndexedAccessOnNamedType(this, self.variant.clone(), idx));
            }
            (Arity::FixedIndexed(_), ChildConstraint::Named(name)) => {
                return Err(TcErr::FieldAccessOnIndexedTyped(this, self.variant.clone(), name));
            }
            (_, ChildConstraint::Unconstrained) | (_, ChildConstraint::NoChildren) => {
                //Nothing to do
            }
        }
        Ok(())
    }

    fn apply_child_constraint_unchecked(&mut self, constraint: ChildConstraint) {
        match constraint {
            ChildConstraint::Indexed(idx) => match &mut self.children {
                Children::Unknown => self.children = Children::Indexed(vec![None; idx]),
                Children::Indexed(children) => ConstraintGraph::<V>::fill_with(children, None, idx),
                Children::Named(_) | Children::None => unreachable!("Mismatch between arity type and children"),
            },
            ChildConstraint::Named(target) => match &mut self.children {
                Children::Unknown => {
                    self.children = Children::Named(HashMap::from_iter(target.iter().map(|k| (k.clone(), None))))
                }
                Children::Named(names) => {
                    names.extend(target.difference(&names.keys().cloned().collect()).cloned().map(|k| (k, None)))
                }
                Children::Indexed(_) | Children::None => unreachable!("Mismatch between arity kind and children"),
            },
            ChildConstraint::Unconstrained | ChildConstraint::NoChildren => {
                // Nothing to do
            }
        }
    }

    fn child_indexed(&self, idx: usize) -> Option<TcKey> {
        debug_assert!(self.children.is_indexed());
        debug_assert!(self.children.len().unwrap_or(0) > idx);
        self.children.indexed().unwrap()[idx]
    }

    fn child_named(&self, name: &str) -> Option<TcKey> {
        debug_assert!(self.children.is_named());
        debug_assert!(self.children.named().unwrap().contains_key(name));
        self.children.named().unwrap()[name]
    }

    fn set_child_indexed(&mut self, n: usize, child: TcKey) {
        debug_assert!(self.children.is_indexed());
        debug_assert!(self.children.len().unwrap_or(0) > n);
        self.children.indexed_mut().unwrap()[n] = Some(child);
    }

    fn set_child_named(&mut self, n: &str, child: TcKey) {
        debug_assert!(self.children.is_named());
        debug_assert!(self.children.named().unwrap().contains_key(n));
        let _ = self.children.named_mut().unwrap().insert(n.to_string(), Some(child));
    }

    fn add_upper_bound(&mut self, bound: TcKey) {
        let _ = self.upper_bounds.insert(bound);
    }

    fn meet(
        &mut self,
        this: TcKey,
        target_key: TcKey,
        rhs: &Self,
        ctx: &V::Context,
    ) -> Result<EquateObligation, TcErr<V>> {
        // TODO: Extremely inefficient; improve.
        let lhs = self;
        let mut is_indexed = true;
        let mut unknown_children = false;
        let mut no_children = false;

        // println!("Meeting: {:?} and {:?}", lhs, rhs);

        match (&lhs.children, &rhs.children) {
            (Children::Indexed(_), Children::Named(_)) | (Children::Named(_), Children::Indexed(_)) => {
                return Err(TcErr::ChildKindMismatch(this, lhs.variant.clone(), target_key, rhs.variant.clone()))
            }
            (Children::Indexed(lhs_c), Children::Indexed(rhs_c)) => {
                debug_assert!(lhs.variant.arity(ctx).to_opt().map(|a| a == lhs_c.len()).unwrap_or(true));
                debug_assert!(rhs.variant.arity(ctx).to_opt().map(|a| a == rhs_c.len()).unwrap_or(true));
            }
            (Children::Named(lhs_c), Children::Named(rhs_c)) => {
                is_indexed = false;
                match (lhs.variant.arity(ctx), rhs.variant.arity(ctx)) {
                    (Arity::FixedNamed(lhs_names), Arity::FixedNamed(rhs_names)) => {
                        debug_assert!(lhs_c.keys().cloned().collect::<HashSet<_>>() == lhs_names);
                        debug_assert!(rhs_c.keys().cloned().collect::<HashSet<_>>() == rhs_names);
                    }
                    _ => {
                        unreachable!("Mismatch between Children and arity")
                    }
                }
            }
            (Children::Named(_), Children::Unknown)
            | (Children::Unknown, Children::Named(_))
            | (Children::None, Children::Named(_))
            | (Children::Named(_), Children::None) => {
                is_indexed = false;
            }
            (Children::Indexed(_), Children::Unknown)
            | (Children::Unknown, Children::Indexed(_))
            | (Children::None, Children::Indexed(_))
            | (Children::Indexed(_), Children::None) => {}
            (Children::Unknown, Children::Unknown) => {
                unknown_children = true;
            }
            (Children::None, Children::Unknown)
            | (Children::Unknown, Children::None)
            | (Children::None, Children::None) => {
                no_children = true;
            }
        }

        let left = Partial { variant: lhs.variant.clone(), children: lhs.children.to_constraint() };
        let right = Partial { variant: rhs.variant.clone(), children: rhs.children.to_constraint() };
        let Partial { variant: new_variant, children: new_constraint } =
            ContextSensitiveVariant::meet(left, right, ctx).map_err(|e| TcErr::Bound(this, Some(target_key), e))?;

        let (mut equates, new_children): (OptEquateObligation, Children) = if unknown_children {
            (vec![], Children::Unknown)
        } else if no_children {
            (vec![], Children::None)
        } else if is_indexed {
            // Make child arrays same length.
            ConstraintGraph::<V>::fill_with(
                lhs.children.indexed_mut().expect("children to be indexed"),
                None,
                rhs.children.len().unwrap_or(0),
            ); // Will be checked later.
            let (equates, new_children) = lhs
                .children
                .indexed()
                .unwrap_or(&vec![])
                .iter()
                .zip(rhs.children.indexed().unwrap_or(&vec![]).iter().chain(std::iter::repeat(&None)))
                .map(|(a, b)| ((*a).zip(*b), (*a).or(*b)))
                .unzip();
            (equates, Children::Indexed(new_children))
        } else {
            let empty_map = HashMap::new();
            let children_l = lhs.children.named().unwrap_or(&empty_map);
            let children_r = rhs.children.named().unwrap_or(&empty_map);
            let (equates, new_children) = children_l
                .keys()
                .chain(children_r.keys())
                .map(|k| {
                    (
                        children_l.get(k).cloned().flatten().zip(children_r.get(k).cloned().flatten()),
                        (
                            k.clone(),
                            children_l.get(k).cloned().flatten().or_else(|| children_r.get(k).cloned().flatten()),
                        ),
                    )
                })
                .unzip();
            (equates, Children::Named(new_children))
        };

        let equates: EquateObligation = equates.drain(..).flatten().collect();

        // commit changes
        lhs.variant = new_variant;
        lhs.children = new_children;
        lhs.upper_bounds.extend(rhs.upper_bounds.iter());
        lhs.apply_child_constraint_checked(target_key, new_constraint, ctx)?;

        // println!("Result: {:?}", lhs);

        debug_assert!(lhs.variant.arity(ctx).to_opt().map(|a| a == lhs.children.len().unwrap_or(0)).unwrap_or(true));

        Ok(equates)
    }

    fn to_partial(&self) -> Partial<V> {
        Partial { variant: self.variant.clone(), children: self.children.to_constraint() }
    }

    fn with_partial(&mut self, this: TcKey, p: Partial<V>, ctx: &V::Context) -> Result<(), TcErr<V>> {
        let Partial { variant, children: constraint } = p;
        match variant.arity(ctx) {
            Arity::Variable => {
                self.variant = variant;
                self.apply_child_constraint_unchecked(constraint); // set_arity increases or is no-op.
                Ok(())
            }
            Arity::None => {
                assert!(matches!(constraint, ChildConstraint::NoChildren));
                if self.children.len().unwrap_or(0) > 0 {
                    return Err(TcErr::ArityMismatch {
                        key: this,
                        variant,
                        inferred_arity: self.children.len().unwrap_or(0),
                        reported_arity: 0,
                    });
                }
                self.variant = variant;
                // self.apply_child_constraint_unchecked(constraint); // set_arity increases or is no-op.
                debug_assert!(self
                    .variant
                    .arity(ctx)
                    .to_opt()
                    .map(|a| a == self.children.len().unwrap_or(0))
                    .unwrap_or(true));
                Ok(())
            }
            Arity::FixedIndexed(arity) => {
                assert_eq!(
                    arity,
                    constraint.len(),
                    "meet of two variants yielded fixed-arity variant that did not match least arity."
                );
                if self.children.len().unwrap_or(0) > arity {
                    return Err(TcErr::ArityMismatch {
                        key: this,
                        variant,
                        inferred_arity: self.children.len().unwrap_or(0),
                        reported_arity: arity,
                    });
                }
                self.variant = variant;
                self.apply_child_constraint_unchecked(constraint); // set_arity increases or is no-op.
                debug_assert!(self
                    .variant
                    .arity(ctx)
                    .to_opt()
                    .map(|a| a == self.children.len().unwrap_or(0))
                    .unwrap_or(true));
                Ok(())
            }
            Arity::FixedNamed(names) => {
                assert_eq!(
                    &names,
                    constraint.names(),
                    "meet of two variants yielded fixed-named variant that did not match required named."
                );
                let keys = self.children.named().map(|m| m.keys().cloned().collect()).unwrap_or_else(HashSet::new);

                if !keys.is_subset(&names) {
                    return Err(TcErr::FieldMismatch {
                        key: this,
                        variant,
                        inferred_fields: keys,
                        reported_fields: names,
                    });
                }
                self.variant = variant;
                self.apply_child_constraint_unchecked(constraint); // set_arity increases or is no-op.
                debug_assert!(self
                    .variant
                    .arity(ctx)
                    .to_opt()
                    .map(|a| a == self.children.len().unwrap_or(0))
                    .unwrap_or(true));
                Ok(())
            }
        }
    }

    fn to_preliminary(&self) -> Preliminary<V> {
        Preliminary { variant: self.variant.clone(), children: self.children.clone() }
    }
}

impl<T: ContextSensitiveVariant> Vertex<T> {
    /// Creates a full vertex without information regarding its children.
    fn new_niladic(this: TcKey) -> Vertex<T> {
        Vertex::Repr(FullVertex { this, ty: Type::top() })
    }
}

impl<T: ContextSensitiveVariant> ConstraintGraph<T> {
    /// Creates an empty constraint graph.
    pub(crate) fn new() -> Self {
        ConstraintGraph { vertices: Vec::new() }
    }

    /// Create an iterator over all keys currently registered in the graph.
    pub(crate) fn all_keys(&self) -> impl Iterator<Item = TcKey> + '_ {
        self.vertices.iter().map(|v| v.this())
    }

    /// Creates and registers a new vertex.
    pub(crate) fn create_vertex(&mut self) -> TcKey {
        self.new_vertex().this()
    }

    fn new_vertex(&mut self) -> &mut Vertex<T> {
        let key = TcKey::new(self.vertices.len());
        let v = Vertex::new_niladic(key);
        self.vertices.push(v);
        self.vertices.last_mut().unwrap() // we just pushed it onto the vec.
    }

    /// Registers that a key has at least `n` children.  If this fact was already known and thus a key is already associated with the child,
    /// the key is returned without calling the `keygen` function.  Otherwise, `keygen` generates a new key which will be added to the graph regularly,
    /// associated with the child, and returned.
    /// If the addition of the child reveals a contradiction, an Err is returned.  An Ok does _not_ indicate the absence of a contradiction.
    pub(crate) fn nth_child(&mut self, parent: TcKey, n: usize, context: &T::Context) -> Result<TcKey, TcErr<T>> {
        let parent_v = self.repr_mut(parent);
        parent_v.ty.apply_child_constraint_checked(parent, ChildConstraint::Indexed(n + 1), context)?; // n is an index, we want an arity of n+1
        let nth_child = parent_v.ty.child_indexed(n);
        if let Some(child) = nth_child {
            return Ok(child);
        }
        let child_key = self.create_vertex();
        self.repr_mut(parent).ty.set_child_indexed(n, child_key);
        Ok(child_key)
    }

    /// Registers that a key has at least this child.  If this fact was already known and thus a key is already associated with the child,
    /// the key is returned without calling the `keygen` function.  Otherwise, `keygen` generates a new key which will be added to the graph regularly,
    /// associated with the child, and returned.
    /// If the addition of the child reveals a contradiction, an Err is returned.  An Ok does _not_ indicate the absence of a contradiction.
    pub(crate) fn named_child(&mut self, parent: TcKey, name: &str, context: &T::Context) -> Result<TcKey, TcErr<T>> {
        let parent_v = self.repr_mut(parent);
        parent_v.ty.apply_child_constraint_checked(
            parent,
            ChildConstraint::Named(HashSet::from([name.to_string()])),
            context,
        )?; // n is an index, we want an arity of n+1
        let child = parent_v.ty.child_named(name);
        if let Some(child) = child {
            return Ok(child);
        }
        let child_key = self.create_vertex();
        self.repr_mut(parent).ty.set_child_named(name, child_key);
        Ok(child_key)
    }

    /// Declares an asymmetric relation between two keys.
    pub(crate) fn add_upper_bound(&mut self, target: TcKey, bound: TcKey) {
        let bound = self.repr(bound).this;
        self.repr_mut(target).ty.add_upper_bound(bound)
    }

    /// Declares a symmetric relation between two keys.
    pub(crate) fn equate(&mut self, left: TcKey, right: TcKey, context: &T::Context) -> Result<(), TcErr<T>> {
        let left = self.repr(left).this;
        let right = self.repr(right).this;
        let (rep, sub) = if left < right { (left, right) } else { (right, left) };
        self.establish_fwd(sub, rep, context)
    }

    /// Imposes an explicit bound on a key.  An Err return indicates a contradiction, an Ok does not indicate the absence of a contradiction.
    pub(crate) fn explicit_bound(&mut self, target: TcKey, bound: T, context: &T::Context) -> Result<(), TcErr<T>> {
        self.add_explicit_bound(target, bound, context).map(|_| ())
    }

    // INTERNAL HELPER FUNCTIONS

    /// Transforms `sub` into a forward to `repr`.
    fn establish_fwd(&mut self, sub: TcKey, repr: TcKey, context: &T::Context) -> Result<(), TcErr<T>> {
        if sub == repr {
            // sub and repr are already in the same eq class since we started
            // out with the identity relation;  nothing to do.
            return Ok(());
        }
        debug_assert_eq!(sub, self.repr(sub).this, "cannot establish a forward for a vertex that already is a forward");
        let mut new_fwd = Vertex::Fwd { this: sub, repr };
        // Replace `sub` vertex with new_fwd.
        std::mem::swap(self.vertex_mut(sub), &mut new_fwd);

        let sub_v = new_fwd.full(); // We asserted it to be a full vertex.
        let repr_v = self.repr_mut(repr);
        // Meet-Alternative: let repr_v = self.repr(repr);

        let equates = repr_v.ty.meet(repr, sub, &sub_v.ty, context)?;
        // Meet-Alternative: let (new_ty, equates) = repr_v.ty.meet(repr, &sub_v.ty)?;
        equates.into_iter().try_for_each(|(a, b)| self.equate(a, b, context))?;

        // Meet-Alternative: self.repr_mut(repr).ty = new_ty;
        Ok(())
    }

    pub(crate) fn lift(&mut self, variant: T, children: Children) -> TcKey {
        let v = self.new_vertex().mut_full();
        v.ty.variant = variant;
        v.ty.children = children;
        v.this
    }

    fn add_explicit_bound(&mut self, target: TcKey, bound: T, context: &T::Context) -> Result<(), TcErr<T>> {
        let target_v = self.repr_mut(target);
        let lhs = target_v.ty.to_partial();
        let rhs_arity = bound.arity(context);
        let rhs = Partial { variant: bound, children: rhs_arity.into() };
        let meet = T::meet(lhs, rhs, context).map_err(|e| TcErr::Bound(target, None, e))?;
        target_v.ty.with_partial(target, meet, context)
    }

    // ACCESS LOGIC

    fn vertex(&self, key: TcKey) -> &Vertex<T> {
        &self.vertices[key.ix]
    }

    fn vertex_mut(&mut self, key: TcKey) -> &mut Vertex<T> {
        &mut self.vertices[key.ix]
    }

    fn repr_mut(&mut self, v: TcKey) -> &mut FullVertex<T> {
        match self.vertex(v).get_repr_nontrans() {
            Some(next) => self.repr_mut(next),
            None => self.vertex_mut(v).mut_full(),
        }
    }

    /// Returns an Iterator over all full vertices in `self`.  This does not resolve forwards, thus every representative only occurs once.
    fn reprs(&self) -> impl Iterator<Item = &FullVertex<T>> {
        self.vertices.iter().filter_map(|v| match v {
            Vertex::Fwd { .. } => None,
            Vertex::Repr(fv) => Some(fv),
        })
    }

    fn repr(&self, v: TcKey) -> &FullVertex<T> {
        match &self.vertex(v) {
            Vertex::Repr(fv) => fv,
            Vertex::Fwd { repr, .. } => self.repr(*repr),
        }
    }

    /// Adds `entry` to `v` until it has length `size`.
    fn fill_with<X: Clone>(v: &mut Vec<X>, entry: X, size: usize) {
        let diff = size.saturating_sub(v.len());
        v.extend(vec![entry; diff]);
    }
}

impl<T: ContextSensitiveVariant> ConstraintGraph<T> {
    /// Starts a fix point computation successively checking and resolving constraints captured in the graph.  
    /// Returns the type table mapping each registered key to a type if no contradiction occurs.
    fn solve_constraints(&mut self, context: T::Context) -> Result<(), TcErr<T>> {
        if self.is_cyclic() {
            return Err(TcErr::CyclicGraph);
        }
        let mut change = true;
        while change {
            change = false;
            change |= self.resolve_asymmetric(&context)?;
        }
        Ok(())
    }

    pub(crate) fn solve_preliminary(mut self, context: T::Context) -> Result<PreliminaryTypeTable<T>, TcErr<T>> {
        self.solve_constraints(context)?;
        Ok(self.construct_preliminary())
    }

    fn construct_preliminary(self) -> PreliminaryTypeTable<T> {
        self.vertices
            .iter()
            .map(|v| v.this())
            .collect::<Vec<TcKey>>()
            .into_iter()
            .map(|key| (key, self.repr(key).ty.to_preliminary()))
            .collect()
    }

    /// Meets all the types of upper bounds with the type of the vertex itself.
    fn resolve_asymmetric(&mut self, context: &T::Context) -> Result<bool, TcErr<T>> {
        self.vertices
            .iter()
            .map(Vertex::this)
            .collect::<Vec<TcKey>>()
            .into_iter()
            .map(|key| {
                let vertex = self.repr(key);
                let initial: (Type<T>, EquateObligation) = (vertex.ty.clone(), Vec::new());
                let (new_type, equates) =
                    vertex.ty.upper_bounds.iter().map(|b| (&self.repr(*b).ty, *b)).fold(Ok(initial), |lhs, rhs| {
                        let (mut old_ty, mut equates) = lhs?;
                        let (rhs, partner_key) = rhs;
                        let new_equates = old_ty.meet(key, partner_key, rhs, context)?;
                        // Meet-Alternative:
                        // let (old_ty, mut equates) = lhs?;
                        // let (new_ty, new_equates) = old_ty.meet(key, rhs)?;
                        equates.extend(new_equates);
                        // Meet-Alternative: Ok((new_ty, equates))
                        Ok((old_ty, equates))
                    })?;
                let change = !Type::equal(&vertex.ty, &new_type, context);
                self.repr_mut(key).ty = new_type;
                equates.into_iter().try_for_each(|(k1, k2)| self.equate(k1, k2, context))?;
                Ok(change)
            })
            .collect::<Result<Vec<bool>, TcErr<T>>>()
            .map(|changes| changes.into_iter().any(|b| b))
    }

    #[must_use]
    fn is_cyclic(&self) -> bool {
        self.vertices.iter().any(|v| self.is_in_loop(v, vec![]))
    }

    fn is_in_loop(&self, vertex: &Vertex<T>, mut history: Vec<TcKey>) -> bool {
        match *vertex {
            Vertex::Fwd { this, repr } => {
                if history.contains(&this) {
                    true
                } else {
                    history.push(this);
                    self.is_in_loop(self.vertex(repr), history)
                }
            }
            Vertex::Repr(FullVertex { this, .. }) => history.contains(&this),
        }
    }
}

impl<V> ConstraintGraph<V>
where
    V: Constructable,
{
    pub(crate) fn solve(mut self, context: V::Context) -> Result<TypeTable<V>, TcErr<V>> {
        self.solve_constraints(context)?;
        self.construct_types()
    }

    fn construct_types(self) -> Result<TypeTable<V>, TcErr<V>> {
        let mut resolved: HashMap<TcKey, V::Type> = HashMap::new();
        let mut open: Vec<&FullVertex<V>> = self.reprs().collect();
        loop {
            let mut still_open = Vec::with_capacity(open.len());
            // println!("Resolved: {:?}", resolved);
            // println!("Open: {:?}", open.iter().map(|d| d.this).collect::<Vec<TcKey>>());
            let num_open = open.len();
            for v in open {
                let children: Result<Option<ResolvedChildren<V::Type>>, TcErr<V>> = match &v.ty.children {
                    Children::Unknown => Ok(Some(ResolvedChildren::None)),
                    Children::None => Ok(Some(ResolvedChildren::None)),
                    Children::Indexed(children) => children
                        .iter()
                        .enumerate()
                        .map(|(ix, c)| {
                            if let Some(key) = c {
                                Ok(resolved.get(&self.repr(*key).this).cloned())
                            } else {
                                V::construct(&V::top(), ResolvedChildren::None)
                                    .map(Some)
                                    .map_err(|e| TcErr::IndexedChildConstruction(v.this, ix, v.ty.to_preliminary(), e))
                            }
                        })
                        .collect(),
                    Children::Named(children) => children
                        .iter()
                        .map(|(name, c)| {
                            if let Some(key) = c {
                                Ok(resolved.get(&self.repr(*key).this).cloned().map(|t| (name.clone(), t)))
                            } else {
                                V::construct(&V::top(), ResolvedChildren::None)
                                    .map(|t| Some((name.clone(), t)))
                                    .map_err(|e| {
                                        TcErr::NamedChildConstruction(v.this, name.clone(), v.ty.to_preliminary(), e)
                                    })
                            }
                        })
                        .collect(),
                };
                if let Some(children) = children? {
                    let ty =
                        v.ty.variant
                            .construct(children)
                            .map_err(|e| TcErr::Construction(v.this, v.ty.to_preliminary(), e))?;
                    let _ = resolved.insert(v.this, ty);
                } else {
                    still_open.push(v)
                }
            }
            if still_open.is_empty() {
                break;
            }
            if still_open.len() == num_open {
                panic!("How tf does this diverge?!");
            }
            open = still_open;
        }
        Ok(self.vertices.iter().map(|v| (v.this(), resolved[&self.repr(v.this()).this].clone())).collect())
    }
}

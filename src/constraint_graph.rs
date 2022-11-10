use crate::{
    types::{Arity, Constructable, ContextSensitiveVariant, Partial, Preliminary, PreliminaryTypeTable, TypeTable},
    TcErr, TcKey,
};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone)]
pub(crate) struct ConstraintGraph<T> {
    vertices: Vec<Vertex<T>>,
}

#[derive(Debug, Clone)]
enum Vertex<T> {
    /// Represents a former vertex that was unified with another one and not chosen to be the representative.
    Fwd { this: TcKey, repr: TcKey },
    /// Represents a full vertex.
    Repr(FullVertex<T>),
}

impl<T> Vertex<T> {
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
struct FullVertex<T> {
    this: TcKey,
    ty: Type<T>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Type<V> {
    variant: V,
    children: Vec<Option<TcKey>>,
    upper_bounds: HashSet<TcKey>,
}

type EquateObligation = Vec<(TcKey, TcKey)>;
type OptEquateObligation = Vec<Option<(TcKey, TcKey)>>;

impl<V: ContextSensitiveVariant> Type<V> {
    fn top() -> Self {
        Type {
            variant: V::top(),
            children: Vec::new(),
            upper_bounds: HashSet::new(),
        }
    }

    fn equal(this: &Self, that: &Self, ctx: &V::Context) -> bool {
        V::equal(&this.variant, &that.variant, ctx)
            && this.children == that.children
            && this.upper_bounds == that.upper_bounds
    }

    fn set_arity_checked(&mut self, this: TcKey, new_arity: usize, ctx: &V::Context) -> Result<(), TcErr<V>> {
        match self.variant.arity(ctx) {
            Arity::Fixed(given_arity) if new_arity > given_arity => {
                return Err(TcErr::ChildAccessOutOfBound(this, self.variant.clone(), new_arity));
            }
            Arity::Fixed(given_arity) => {
                ConstraintGraph::<V>::fill_with(&mut self.children, None, given_arity)
            }
            Arity::Variable => {
                ConstraintGraph::<V>::fill_with(&mut self.children, None, new_arity)
            }
        }
        Ok(())
    }

    fn set_arity_unchecked(&mut self, new_arity: usize) {
        ConstraintGraph::<V>::fill_with(&mut self.children, None, new_arity);
    }

    fn child(&self, n: usize) -> Option<TcKey> {
        debug_assert!(n < self.children.len());
        self.children[n]
    }

    fn set_child(&mut self, n: usize, child: TcKey) {
        debug_assert!(n < self.children.len());
        self.children[n] = Some(child);
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
        let left_arity = lhs.children.len();
        let right_arity = rhs.children.len();

        debug_assert!(lhs.variant.arity(ctx).to_opt().map(|a| a == left_arity).unwrap_or(true));
        debug_assert!(rhs.variant.arity(ctx).to_opt().map(|a| a == right_arity).unwrap_or(true));

        let left = Partial { variant: lhs.variant.clone(), least_arity: left_arity };
        let right = Partial { variant: rhs.variant.clone(), least_arity: right_arity };
        let Partial { variant: new_variant, least_arity } =
            ContextSensitiveVariant::meet(left, right, ctx).map_err(|e| TcErr::Bound(this, Some(target_key), e))?;

        // Make child arrays same length.
        // Will be checked later.
        ConstraintGraph::<V>::fill_with(&mut lhs.children, None, right_arity);

        let (equates, new_children): (OptEquateObligation, Vec<Option<TcKey>>) = lhs
            .children
            .iter()
            .zip(rhs.children.iter().copied().chain(std::iter::repeat(None)))
            .map(|(a, b)| (a.zip(b), a.or(b)))
            .unzip();

        let equates: EquateObligation = equates.into_iter().flatten().collect();

        // commit changes
        lhs.variant = new_variant;
        lhs.children = new_children;
        lhs.upper_bounds.extend(rhs.upper_bounds.iter());
        lhs.set_arity_checked(target_key, least_arity, ctx)?;

        debug_assert!(
            lhs.variant.arity(ctx).to_opt().map(|a| a == lhs.children.len()).unwrap_or(true)
        );

        Ok(equates)
    }

    fn to_partial(&self) -> Partial<V> {
        Partial {
            variant: self.variant.clone(),
            least_arity: self.children.len(),
        }
    }

    fn with_partial(&mut self, this: TcKey, p: Partial<V>, ctx: &V::Context) -> Result<(), TcErr<V>> {
        let Partial { variant, least_arity } = p;

        match variant.arity(ctx) {
            Arity::Variable => {
                self.variant = variant;
                self.set_arity_unchecked(least_arity); // set_arity increases or is no-op.
                Ok(())
            }
            Arity::Fixed(arity) => {
                assert_eq!(
                    arity, least_arity,
                    "meet of two variants yielded fixed-arity variant that did not match least arity."
                );
                if self.children.len() > arity {
                    return Err(TcErr::ArityMismatch {
                        key: this,
                        variant,
                        inferred_arity: self.children.len(),
                        reported_arity: least_arity,
                    });
                }

                self.variant = variant;
                self.set_arity_unchecked(least_arity); // set_arity increases or is no-op.

                debug_assert!(
                    self.variant.arity(ctx).to_opt().map(|a| a == self.children.len()).unwrap_or(true)
                );

                Ok(())
            }
        }
    }

    fn to_preliminary(&self) -> Preliminary<V> {
        Preliminary {
            variant: self.variant.clone(),
            children: self.children.clone(),
        }
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
        parent_v.ty.set_arity_checked(parent, n + 1, context)?; // n is an index, we want an arity of n+1
        let nth_child = parent_v.ty.child(n);
        if let Some(child) = nth_child {
            return Ok(child);
        }
        let child_key = self.create_vertex();
        self.repr_mut(parent).ty.set_child(n, child_key);
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
        self.add_explicit_bound(target, bound, context).map(drop)
    }

    // INTERNAL HELPER FUNCTIONS

    /// Transforms `sub` into a forward to `repr`.
    fn establish_fwd(&mut self, sub: TcKey, repr: TcKey, context: &T::Context) -> Result<(), TcErr<T>> {
        if sub == repr {
            // sub and repr are already in the same eq class since we started
            // out with the identity relation;  nothing to do.
            return Ok(());
        }

        debug_assert_eq!(
            sub, self.repr(sub).this,
            "cannot establish a forward for a vertex that already is a forward"
        );

        let mut new_fwd = Vertex::Fwd { this: sub, repr };
        // Replace `sub` vertex with new_fwd.
        core::mem::swap(self.vertex_mut(sub), &mut new_fwd);

        let sub_v = new_fwd.full(); // We asserted it to be a full vertex.
        let repr_v = self.repr_mut(repr);

        let equates = repr_v.ty.meet(repr, sub, &sub_v.ty, context)?;
        equates.into_iter().try_for_each(|(a, b)| self.equate(a, b, context))?;

        Ok(())
    }

    pub(crate) fn lift(&mut self, variant: T, children: Vec<Option<TcKey>>) -> TcKey {
        let v = self.new_vertex().mut_full();
        v.ty.variant = variant;
        v.ty.children = children;
        v.this
    }

    fn add_explicit_bound(&mut self, target: TcKey, bound: T, context: &T::Context) -> Result<(), TcErr<T>> {
        let target_v = self.repr_mut(target);
        let lhs = target_v.ty.to_partial();
        let rhs_arity = bound.arity(context).to_opt().unwrap_or(0);
        let rhs = Partial { variant: bound, least_arity: rhs_arity };
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
        match *self.vertex(v) {
            Vertex::Repr(ref fv) => fv,
            Vertex::Fwd { repr, .. } => self.repr(repr),
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
            change = self.resolve_asymmetric(&context)?;
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
            .map(Vertex::this)
            .map(|key| (key, self.repr(key).ty.to_preliminary()))
            .collect()
    }

    /// Meets all the types of upper bounds with the type of the vertex itself.
    fn resolve_asymmetric(&mut self, context: &T::Context) -> Result<bool, TcErr<T>> {
        self.vertices
            .iter()
            .map(Vertex::this)
            .collect::<Vec<_>>() // necessary because both mapped closures need mutable access
            .into_iter()
            .map(|key| {
                let vertex = self.repr(key);
                let initial: (Type<T>, EquateObligation) = (vertex.ty.clone(), Vec::new());
                let (new_type, equates) = vertex.ty.upper_bounds
                    .iter()
                    .copied()
                    .map(|b| (&self.repr(b).ty, b))
                    .try_fold(initial, |lhs, rhs| {
                        let (mut old_ty, mut equates) = lhs;
                        let (rhs, partner_key) = rhs;
                        let new_equates = old_ty.meet(key, partner_key, rhs, context)?;
                        equates.extend(new_equates);
                        Ok((old_ty, equates))
                    })?;

                let change = !Type::equal(&vertex.ty, &new_type, context);

                self.repr_mut(key).ty = new_type;

                equates
                    .into_iter().
                    try_for_each(|(k1, k2)| self.equate(k1, k2, context))?;

                Ok(change)
            })
            .try_fold(false, |acc, chg| Ok(acc || chg?))
    }

    #[must_use]
    fn is_cyclic(&self) -> bool {
        self.vertices.iter().any(|v| self.is_in_loop(v, Vec::new()))
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
            let num_open = open.len();

            for v in open {
                let children = v.ty.children
                    .iter()
                    .enumerate()
                    .map(|(ix, c)| {
                        if let Some(key) = c {
                            Ok(resolved.get(&self.repr(*key).this).cloned())
                        } else {
                            V::construct(&V::top(), &[])
                                .map(Some)
                                .map_err(|e| {
                                    TcErr::ChildConstruction(v.this, ix, v.ty.to_preliminary(), e)
                                })
                        }
                    })
                    .collect::<Result<Option<Vec<V::Type>>, TcErr<V>>>()?;

                if let Some(children) = children {
                    let ty = v.ty.variant
                        .construct(&children)
                        .map_err(|e| {
                            TcErr::Construction(v.this, v.ty.to_preliminary(), e)
                        })?;

                    let _ = resolved.insert(v.this, ty);
                } else {
                    still_open.push(v);
                }
            }

            if still_open.is_empty() {
                break;
            }

            if still_open.len() == num_open {
                unreachable!("Solver fixpoint iteration diverged?!");
            }

            open = still_open;
        }

        let result = self
            .vertices
            .iter()
            .map(|v| {
                let this = v.this();
                (this, resolved[&self.repr(this).this].clone())
            })
            .collect();

        Ok(result)
    }
}

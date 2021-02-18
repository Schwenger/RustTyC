use crate::{
    types::Partial,
    types::{Constructable, Preliminary, PreliminaryTypeTable, TypeTable, Variant},
    TcErr, TcKey,
};
use std::collections::HashMap;

#[cfg(not(test))]
use log::trace;

#[cfg(test)]
use std::println as trace;

#[derive(Debug, Clone)]
pub(crate) struct ConstraintGraph<T: Variant> {
    vertices: Vec<Vertex<T>>,
}

#[derive(Debug, Clone)]
enum Vertex<T: Variant> {
    /// Represents a former vertex that was unified with another one and not chosen to be the representative.
    Fwd { this: TcKey, repr: TcKey },
    /// Represents a full vertex.
    Repr(FullVertex<T>),
}

impl<T: Variant> Vertex<T> {
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
struct FullVertex<T: Variant> {
    this: TcKey,
    ty: Type<T>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Type<V: Variant> {
    variant: V,
    children: Vec<Option<TcKey>>,
    upper_bounds: Vec<TcKey>,
}

type EquateObligation = Vec<(TcKey, TcKey)>;
impl<V: Variant> Type<V> {
    fn top() -> Self {
        Type { variant: V::top(), children: Vec::new(), upper_bounds: Vec::new() }
    }

    fn set_arity(&mut self, this: TcKey, n: usize) -> Result<(), TcErr<V>> {
        trace!("Setting arity of {:?} to {}", this, n);
        if n > self.children.len() && self.variant.fixed_arity() {
            return Err(TcErr::ChildAccessOutOfBound(this, self.variant.clone(), n));
        }
        ConstraintGraph::<V>::fill_with(&mut self.children, None, n);
        Ok(())
    }

    fn child(&self, n: usize) -> Option<TcKey> {
        trace!("Accessing child {} of variant {:?}", n, &self.variant);
        debug_assert!(self.children.len() > n);
        self.children[n]
    }

    fn set_child(&mut self, n: usize, child: TcKey) {
        trace!("Setting child {} of variant {:?} to {:?}", n, &self.variant, child);
        debug_assert!(self.children.len() > n);
        self.children[n] = Some(child);
    }

    fn add_upper_bound(&mut self, bound: TcKey) {
        trace!("Adding upper bound {:?} to variant {:?}", bound, &self.variant);
        self.upper_bounds.push(bound);
    }

    fn meet(&self, target_key: TcKey, rhs: &Self) -> Result<(Self, EquateObligation), TcErr<V>> {
        trace!("Meeting the variants {:?} and {:?} for {:?},", &self.variant, &rhs.variant, target_key);
        // TODO: Extremely inefficient; improve.
        let lhs = self;
        let left_arity = lhs.children.len();
        let right_arity = rhs.children.len();
        let left = Partial { variant: lhs.variant.clone(), least_arity: left_arity };
        let right = Partial { variant: rhs.variant.clone(), least_arity: right_arity };
        let Partial { variant, least_arity } =
            Variant::meet(left, right).map_err(|e| TcErr::Bound(target_key, None, e))?;

        let zipped = lhs.children.iter().zip(rhs.children.iter());
        let equates: EquateObligation = zipped.clone().flat_map(|(a, b)| a.zip(*b)).collect();
        let children: Vec<Option<TcKey>> = zipped.map(|(a, b)| a.or(*b)).collect();
        let upper_bounds: Vec<TcKey> = lhs.upper_bounds.iter().chain(rhs.upper_bounds.iter()).cloned().collect();

        let mut res = Self { variant, children, upper_bounds };
        res.set_arity(target_key, least_arity)?;

        trace!("Created {:?}", res);
        Ok((res, equates))
    }

    fn to_partial(&self) -> Partial<V> {
        Partial { variant: self.variant.clone(), least_arity: self.children.len() }
    }

    fn with_partial(&mut self, this: TcKey, p: Partial<V>) -> Result<(), TcErr<V>> {
        trace!("Incorporating partial {:?} into {:?} with variant {:?}", &p, this, &self.variant);
        let Partial { variant, least_arity } = p;
        if self.children.len() > least_arity && variant.fixed_arity() {
            return Err(TcErr::ArityMismatch {
                key: this,
                variant,
                inferred_arity: self.children.len(),
                reported_arity: least_arity,
            });
        }
        self.variant = variant;
        trace!("Is now variant {:?}.", &self.variant);
        self.set_arity(this, least_arity)
    }

    fn to_preliminary(&self) -> Preliminary<V> {
        Preliminary { variant: self.variant.clone(), children: self.children.clone() }
    }
}

impl<T: Variant> Vertex<T> {
    /// Creates a full vertex without information regarding its children.
    fn new_niladic(this: TcKey) -> Vertex<T> {
        Vertex::Repr(FullVertex { this, ty: Type::top() })
    }
}

impl<T: Variant> ConstraintGraph<T> {
    /// Creates an empty constraint graph.
    pub(crate) fn new() -> ConstraintGraph<T> {
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
        trace!("Created new key: {:?}", key);
        self.vertices.last_mut().unwrap() // we just pushed it onto the vec.
    }

    /// Registers that a key has at least `n` children.  If this fact was already known and thus a key is already associated with the child,
    /// the key is returned without calling the `keygen` function.  Otherwise, `keygen` generates a new key which will be added to the graph regularly,
    /// associated with the child, and returned.
    /// If the addition of the child reveals a contradiction, an Err is returned.  An Ok does _not_ indicate the absence of a contradiction.
    pub(crate) fn nth_child(&mut self, parent: TcKey, n: usize) -> Result<TcKey, TcErr<T>> {
        let parent_v = self.repr_mut(parent);
        parent_v.ty.set_arity(parent, n)?;
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
    pub(crate) fn equate(&mut self, left: TcKey, right: TcKey) -> Result<(), TcErr<T>> {
        let left = self.repr(left).this;
        let right = self.repr(right).this;
        let (rep, sub) = if left < right { (left, right) } else { (right, left) };
        self.establish_fwd(sub, rep)
    }

    /// Imposes an explicit bound on a key.  An Err return indicates a contradiction, an Ok does not indicate the absence of a contradiction.
    pub(crate) fn explicit_bound(&mut self, target: TcKey, bound: T) -> Result<(), TcErr<T>> {
        self.add_explicit_bound(target, bound).map(|_| ())
    }

    // INTERNAL HELPER FUNCTIONS

    /// Transforms `sub` into a forward to `repr`.
    fn establish_fwd(&mut self, sub: TcKey, repr: TcKey) -> Result<(), TcErr<T>> {
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
        let repr_v = self.repr(repr);

        let (new_ty, equates) = repr_v.ty.meet(repr, &sub_v.ty)?;
        equates.into_iter().try_for_each(|(a, b)| self.equate(a, b))?;

        self.repr_mut(repr).ty = new_ty;
        Ok(())
    }

    pub(crate) fn lift(&mut self, variant: T, children: Vec<Option<TcKey>>) -> TcKey {
        let v = self.new_vertex().mut_full();
        v.ty.variant = variant;
        v.ty.children = children;
        v.this
    }

    fn add_explicit_bound(&mut self, target: TcKey, bound: T) -> Result<(), TcErr<T>> {
        let target_v = self.repr_mut(target);
        let lhs = target_v.ty.to_partial();
        let rhs = Partial { variant: bound, least_arity: target_v.ty.children.len() };
        let meet = T::meet(lhs, rhs).map_err(|e| TcErr::Bound(target, None, e))?;
        target_v.ty.with_partial(target, meet)
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

impl<T: Variant> ConstraintGraph<T> {
    /// Starts a fix point computation successively checking and resolving constraints captured in the graph.  
    /// Returns the type table mapping each registered key to a type if no contradiction occurs.
    fn solve_constraints(&mut self) -> Result<(), TcErr<T>> {
        let mut change = true;
        while change {
            change = false;
            change |= self.resolve_asymmetric()?;
        }
        Ok(())
    }

    pub(crate) fn solve_preliminary(mut self) -> Result<PreliminaryTypeTable<T>, TcErr<T>> {
        self.solve_constraints()?;
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
    fn resolve_asymmetric(&mut self) -> Result<bool, TcErr<T>> {
        self.vertices
            .iter()
            .map(Vertex::this)
            .collect::<Vec<TcKey>>()
            .into_iter()
            .map(|key| {
                let vertex = self.repr(key);
                let initial: (Type<T>, EquateObligation) = (vertex.ty.clone(), Vec::new());
                let (new_type, equates) =
                    vertex.ty.upper_bounds.iter().map(|b| &self.repr(*b).ty).fold(Ok(initial), |lhs, rhs| {
                        let (old_ty, mut equates) = lhs?;
                        let (new_ty, new_equates) = old_ty.meet(key, rhs)?;
                        equates.extend(new_equates);
                        Ok((new_ty, equates))
                    })?;
                trace!("Incorporating asym data. {:?} became {:?}.", &vertex.ty, &new_type);
                let change = vertex.ty != new_type;
                trace!("Change detected: {}.", change);
                self.repr_mut(key).ty = new_type;
                equates.into_iter().try_for_each(|(k1, k2)| self.equate(k1, k2))?;
                Ok(change)
            })
            .collect::<Result<Vec<bool>, TcErr<T>>>()
            .map(|changes| changes.into_iter().any(|b| b))
    }
}

impl<V> ConstraintGraph<V>
where
    V: Variant + Constructable,
{
    pub(crate) fn solve(mut self) -> Result<TypeTable<V>, TcErr<V>> {
        self.solve_constraints()?;
        self.construct_types()
    }

    fn construct_types(self) -> Result<TypeTable<V>, TcErr<V>> {
        let mut resolved: HashMap<TcKey, V::Type> = HashMap::new();
        let mut open: Vec<&FullVertex<V>> = self.reprs().collect();
        let top = V::top().construct(&[]).map_err(|e| TcErr::Construction(Preliminary::top(), e))?;
        loop {
            let mut still_open = Vec::with_capacity(open.len());
            let num_open = open.len();
            for v in open {
                let children: Vec<&V::Type> =
                    v.ty.children
                        .iter()
                        .flat_map(|c| if let Some(ck) = c { resolved.get(ck) } else { Some(&top) })
                        .collect();
                if v.ty.children.len() == children.len() {
                    let children = children.into_iter().cloned().collect::<Vec<V::Type>>();
                    let ty =
                        v.ty.variant.construct(&children).map_err(|e| TcErr::Construction(v.ty.to_preliminary(), e))?;
                    resolved.insert(v.this, ty);
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

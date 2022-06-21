use crate::children::{Children, ChildConstraint};
use crate::type_table::{TypeTable, PreliminaryTypeTable, Constructable, ResolvedChildren};
use crate::{
    types::{ContextType, Infered},
    TcErr, Key,
};
use std::collections::{HashMap, HashSet};


mod type_info;
use type_info::TypeInfo;


type EquateObligation = Vec<(Key, Key)>;
type OptEquateObligation = Vec<Option<(Key, Key)>>;

#[derive(Debug, Clone)]
pub(crate) struct ConstraintGraph<T: ContextType> {
    vertices: Vec<Vertex<T>>,

    /// Child id is the index of its name
    child_names: Vec<String>,
    /// Maps the child name to its index
    child_ids: HashMap<String, usize>,
}

#[derive(Debug, Clone)]
pub(crate) enum Vertex<T: ContextType> {
    /// Represents a former vertex that was unified with another one and not chosen to be the representative.
    Fwd { this: Key, repr: Key },
    /// Represents a full vertex.
    Repr(FullVertex<T>),
}

impl<T: ContextType> Vertex<T> {
    fn this(&self) -> Key {
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
    fn get_repr_nontrans(&self) -> Option<Key> {
        match self {
            Vertex::Fwd { repr, .. } => Some(*repr),
            Vertex::Repr(_) => None,
        }
    }
    /// Creates a full vertex without information regarding its children.
    fn new_niladic(this: Key) -> Vertex<T> {
        Vertex::Repr(FullVertex { this, ty: TypeInfo::top() })
    }
}

#[derive(Debug, Clone)]
pub(crate) struct FullVertex<T: ContextType> {
    this: Key,
    ty: TypeInfo<T>,
}


impl<T: ContextType> ConstraintGraph<T> {
    /// Creates an empty constraint graph.
    pub(crate) fn new() -> Self {
        ConstraintGraph { vertices: Vec::new(), child_names: Vec::new(), child_ids: HashMap::new() }
    }

    /// Defines all possible names that should be allowed for child accesses.
    pub(crate) fn define_children_names(&mut self, child_names: &[String], child_ids: &HashMap<String, usize>) {
        self.child_names = child_names.to_vec();
        self.child_ids = child_ids.clone();
    }

    /// Create an iterator over all keys currently registered in the graph.
    pub(crate) fn all_keys(&self) -> impl Iterator<Item = Key> + '_ {
        self.vertices.iter().map(|v| v.this())
    }

    /// Creates and registers a new vertex.
    pub(crate) fn create_vertex(&mut self) -> Key {
        self.new_vertex().this()
    }

    fn new_vertex(&mut self) -> &mut Vertex<T> {
        let key = Key::new(self.vertices.len());
        let v = Vertex::new_niladic(key);
        self.vertices.push(v);
        self.vertices.last_mut().unwrap() // we just pushed it onto the vec.
    }

    /// Registers that a key has at least `n` children.  If this fact was already known and thus a key is already associated with the child,
    /// the key is returned without calling the `keygen` function.  Otherwise, `keygen` generates a new key which will be added to the graph regularly,
    /// associated with the child, and returned.
    /// If the addition of the child reveals a contradiction, an Err is returned.  An Ok does _not_ indicate the absence of a contradiction.
    pub(crate) fn nth_child(&mut self, parent: Key, n: usize, context: &T::Context) -> Result<Key, TcErr<T>> {
        let parent_v = Self::repr_mut(&mut self.vertices, parent);
        parent_v.ty.apply_child_constraint_checked(
            parent,
            ChildConstraint::Indexed(n + 1),
            context,
            &self.child_ids,
            &self.child_names,
        )?; // n is an index, we want an arity of n+1
        let nth_child = parent_v.ty.child_indexed(n);
        if let Some(child) = nth_child {
            return Ok(child);
        }
        let child_key = self.create_vertex();
        Self::repr_mut(&mut self.vertices, parent).ty.set_child_indexed(n, child_key);
        Ok(child_key)
    }

    /// Registers that a key has at least this child.  If this fact was already known and thus a key is already associated with the child,
    /// the key is returned without calling the `keygen` function.  Otherwise, `keygen` generates a new key which will be added to the graph regularly,
    /// associated with the child, and returned.
    /// If the addition of the child reveals a contradiction, an Err is returned.  An Ok does _not_ indicate the absence of a contradiction.
    pub(crate) fn named_child(&mut self, parent: Key, name: &str, context: &T::Context) -> Result<Key, TcErr<T>> {
        let ConstraintGraph { vertices, child_ids, child_names } = self;
        let parent_v = Self::repr_mut(vertices, parent);

        let id = *child_ids.get(name).ok_or_else(|| TcErr::UnknownField(parent, name.to_string()))?;

        parent_v.ty.apply_child_constraint_checked(
            parent,
            ChildConstraint::Named(HashSet::from([id])),
            context,
            child_ids,
            child_names,
        )?; // n is an index, we want an arity of n+1
        let child = parent_v.ty.child_named(id);
        if let Some(child) = child {
            return Ok(child);
        }
        let child_key = self.create_vertex();
        Self::repr_mut(&mut self.vertices, parent).ty.set_child_named(id, child_key);
        Ok(child_key)
    }

    /// Declares an asymmetric relation between two keys.
    pub(crate) fn add_upper_bound(&mut self, target: Key, bound: Key) {
        let bound = self.repr(bound).this;
        Self::repr_mut(&mut self.vertices, target).ty.add_upper_bound(bound)
    }

    /// Declares a symmetric relation between two keys.
    pub(crate) fn equate(&mut self, left: Key, right: Key, context: &T::Context) -> Result<(), TcErr<T>> {
        let left = self.repr(left).this;
        let right = self.repr(right).this;
        let (rep, sub) = if left < right { (left, right) } else { (right, left) };
        self.establish_fwd(sub, rep, context)
    }

    /// Imposes an explicit bound on a key.  An Err return indicates a contradiction, an Ok does not indicate the absence of a contradiction.
    pub(crate) fn explicit_bound(&mut self, target: Key, bound: T, context: &T::Context) -> Result<(), TcErr<T>> {
        self.add_explicit_bound(target, bound, context).map(|_| ())
    }

    // INTERNAL HELPER FUNCTIONS

    /// Transforms `sub` into a forward to `repr`.
    fn establish_fwd(&mut self, sub: Key, repr: Key, context: &T::Context) -> Result<(), TcErr<T>> {
        if sub == repr {
            // sub and repr are already in the same eq class since we started
            // out with the identity relation;  nothing to do.
            return Ok(());
        }
        debug_assert_eq!(sub, self.repr(sub).this, "cannot establish a forward for a vertex that already is a forward");
        let mut new_fwd = Vertex::Fwd { this: sub, repr };
        // Replace `sub` vertex with new_fwd.
        std::mem::swap(Self::vertex_mut(&mut self.vertices, sub), &mut new_fwd);

        let sub_v = new_fwd.full(); // We asserted it to be a full vertex.
        let repr_v = Self::repr_mut(&mut self.vertices, repr);
        // Meet-Alternative: let repr_v = self.repr(repr);

        let equates = repr_v.ty.meet(repr, sub, &sub_v.ty, context, &self.child_ids, &self.child_names)?;
        // Meet-Alternative: let (new_ty, equates) = repr_v.ty.meet(repr, &sub_v.ty)?;
        equates.into_iter().try_for_each(|(a, b)| self.equate(a, b, context))?;

        // Meet-Alternative: self.repr_mut(repr).ty = new_ty;
        Ok(())
    }

    pub(crate) fn lift(&mut self, variant: T, children: Children) -> Key {
        let v = self.new_vertex().mut_full();
        v.ty.variant = variant;
        v.ty.children = children;
        v.this
    }

    fn add_explicit_bound(&mut self, target: Key, bound: T, context: &T::Context) -> Result<(), TcErr<T>> {
        let target_v = Self::repr_mut(&mut self.vertices, target);
        let lhs = target_v.ty.to_infered();
        let rhs_arity = bound.arity(context);
        let rhs = Infered { variant: bound, children: rhs_arity.substitute(&self.child_ids).into() };
        let meet = T::meet(lhs, rhs, context).map_err(|e| TcErr::Bound(target, None, e))?;
        target_v.ty.with_infered(target, meet, context, &self.child_ids, &self.child_names)
    }

    // ACCESS LOGIC

    fn vertex(vertices: &[Vertex<T>], key: Key) -> &Vertex<T> {
        &vertices[key.ix]
    }

    fn vertex_mut(vertices: &mut Vec<Vertex<T>>, key: Key) -> &mut Vertex<T> {
        &mut vertices[key.ix]
    }

    fn repr_mut(vertices: &mut Vec<Vertex<T>>, v: Key) -> &mut FullVertex<T> {
        match Self::vertex(vertices, v).get_repr_nontrans() {
            Some(next) => Self::repr_mut(vertices, next),
            None => Self::vertex_mut(vertices, v).mut_full(),
        }
    }

    /// Returns an Iterator over all full vertices in `self`.  This does not resolve forwards, thus every representative only occurs once.
    fn reprs(&self) -> impl Iterator<Item = &FullVertex<T>> {
        self.vertices.iter().filter_map(|v| match v {
            Vertex::Fwd { .. } => None,
            Vertex::Repr(fv) => Some(fv),
        })
    }

    fn repr(&self, v: Key) -> &FullVertex<T> {
        match &Self::vertex(&self.vertices, v) {
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

impl<T: ContextType> ConstraintGraph<T> {
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
            .collect::<Vec<Key>>()
            .into_iter()
            .map(|key| (key, self.repr(key).ty.to_preliminary()))
            .collect()
    }

    /// Meets all the types of upper bounds with the type of the vertex itself.
    fn resolve_asymmetric(&mut self, context: &T::Context) -> Result<bool, TcErr<T>> {
        self.vertices
            .iter()
            .map(Vertex::this)
            .collect::<Vec<Key>>()
            .into_iter()
            .map(|key| {
                let vertex = self.repr(key);
                let initial: (TypeInfo<T>, EquateObligation) = (vertex.ty.clone(), Vec::new());
                let (new_type, equates) =
                    vertex.ty.upper_bounds.iter().map(|b| (&self.repr(*b).ty, *b)).fold(Ok(initial), |lhs, rhs| {
                        let (mut old_ty, mut equates) = lhs?;
                        let (rhs, partner_key) = rhs;
                        let new_equates =
                            old_ty.meet(key, partner_key, rhs, context, &self.child_ids, &self.child_names)?;
                        // Meet-Alternative:
                        // let (old_ty, mut equates) = lhs?;
                        // let (new_ty, new_equates) = old_ty.meet(key, rhs)?;
                        equates.extend(new_equates);
                        // Meet-Alternative: Ok((new_ty, equates))
                        Ok((old_ty, equates))
                    })?;
                let change = !TypeInfo::equal(&vertex.ty, &new_type, context);
                Self::repr_mut(&mut self.vertices, key).ty = new_type;
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

    fn is_in_loop(&self, vertex: &Vertex<T>, mut history: Vec<Key>) -> bool {
        match *vertex {
            Vertex::Fwd { this, repr } => {
                if history.contains(&this) {
                    true
                } else {
                    history.push(this);
                    self.is_in_loop(Self::vertex(&self.vertices, repr), history)
                }
            }
            Vertex::Repr(FullVertex { this, .. }) => history.contains(&this),
        }
    }
}

impl<T> ConstraintGraph<T>
where
    T: Constructable,
{
    pub(crate) fn solve(mut self, context: T::Context) -> Result<TypeTable<T>, TcErr<T>> {
        self.solve_constraints(context)?;
        self.construct_types()
    }

    fn construct_types(self) -> Result<TypeTable<T>, TcErr<T>> {
        let mut resolved: HashMap<Key, T::Type> = HashMap::new();
        let mut open: Vec<&FullVertex<T>> = self.reprs().collect();
        loop {
            let mut still_open = Vec::with_capacity(open.len());
            // println!("Resolved: {:?}", resolved);
            // println!("Open: {:?}", open.iter().map(|d| d.this).collect::<Vec<TcKey>>());
            let num_open = open.len();
            for v in open {
                let children: Result<Option<ResolvedChildren<T::Type>>, TcErr<T>> = match &v.ty.children {
                    Children::Unknown => Ok(Some(ResolvedChildren::None)),
                    Children::None => Ok(Some(ResolvedChildren::None)),
                    Children::Indexed(children) => children
                        .iter()
                        .enumerate()
                        .map(|(ix, c)| {
                            if let Some(key) = c {
                                Ok(resolved.get(&self.repr(*key).this).cloned())
                            } else {
                                T::construct(&T::top(), ResolvedChildren::None)
                                    .map(Some)
                                    .map_err(|e| TcErr::IndexedChildConstruction(v.this, ix, v.ty.to_preliminary(), e))
                            }
                        })
                        .collect(),
                    Children::Named(children) => children
                        .iter()
                        .map(|(name, c)| {
                            if let Some(key) = c {
                                Ok(resolved
                                    .get(&self.repr(*key).this)
                                    .cloned()
                                    .map(|t| (self.child_names[*name].clone(), t)))
                            } else {
                                T::construct(&T::top(), ResolvedChildren::None)
                                    .map(|t| Some((self.child_names[*name].clone(), t)))
                                    .map_err(|e| {
                                        TcErr::NamedChildConstruction(
                                            v.this,
                                            self.child_names[*name].clone(),
                                            v.ty.to_preliminary(),
                                            e,
                                        )
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

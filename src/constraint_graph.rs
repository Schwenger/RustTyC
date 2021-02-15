use crate::types::Abstract;
use crate::{TcErr, TcKey};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(crate) struct ConstraintGraph<T: Abstract> {
    vertices: Vec<Vertex<T>>,
}

#[derive(Debug, Clone)]
enum Vertex<T: Abstract> {
    /// Represents a former vertex that was unified with another one and not chosen to be the representative.
    Fwd { this: TcKey, repr: TcKey },
    /// Represents a full vertex.
    Repr(FullVertex<T>),
}

impl<T: Abstract> Vertex<T> {
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

    /// Returns the reference of the vertex representing this one.  Returns None if this vertex represents itself.
    fn get_repr_nontrans(&self) -> Option<TcKey> {
        match self {
            Vertex::Fwd { repr, .. } => Some(*repr),
            Vertex::Repr(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
struct FullVertex<T: Abstract> {
    children: Vec<Option<TcKey>>,
    upper_bounds: Vec<TcKey>,
    this: TcKey,
    ty: T,
    exact_bound: Option<T>,
}

impl<T: Abstract> Vertex<T> {
    /// Creates a full vertex without information regarding its children.
    fn new_niladic(this: TcKey) -> Vertex<T> {
        Vertex::Repr(FullVertex {
            children: Vec::new(),
            upper_bounds: Vec::new(),
            this,
            ty: T::unconstrained(),
            exact_bound: None,
        })
    }
}

impl<T: Abstract> ConstraintGraph<T> {
    /// Creates an empty constraint graph.
    pub(crate) fn new() -> ConstraintGraph<T> {
        ConstraintGraph { vertices: Vec::new() }
    }

    /// Create an iterator over all keys currently registered in the graph.
    pub(crate) fn all_keys(&self) -> impl Iterator<Item = TcKey> + '_ {
        self.vertices.iter().map(|v| v.this())
    }

    /// Creates and registers a new vertex.
    pub(crate) fn new_vertex(&mut self) -> TcKey {
        let key = TcKey::new(self.vertices.len());
        let v = Vertex::new_niladic(key);
        self.add_vertex(v);
        key
    }

    /// Registers that a key has at least `n` children.  If this fact was already known and thus a key is already associated with the child,
    /// the key is returned without calling the `keygen` function.  Otherwise, `keygen` generates a new key which will be added to the graph regularly,
    /// associated with the child, and returned.
    /// If the addition of the child reveals a contradiction, an Err is returned.  An Ok does _not_ indicate the absence of a contradiction.
    pub(crate) fn nth_child(&mut self, parent: TcKey, nth: usize) -> Result<TcKey, TcErr<T>> {
        let parent_v = self.repr_mut(parent);
        if parent_v.ty.arity().map(|ar| ar < nth).unwrap_or(false) {
            return Err(TcErr::ChildAccessOutOfBound(parent, parent_v.ty.clone(), nth));
        }
        let required_length = nth + 1;
        Self::fill_with(&mut parent_v.children, None, required_length);
        let nth_child = parent_v.children[nth];
        if let Some(child) = nth_child {
            return Ok(child);
        }
        let key = self.new_vertex();
        let vertex = self.vertex(key).this();
        self.repr_mut(parent).children[nth] = Some(vertex);
        Ok(key)
    }

    /// Declares an asymmetric relation between two keys.
    pub(crate) fn add_upper_bound(&mut self, target: TcKey, bound: TcKey) {
        let bound = self.repr(bound).this;
        self.repr_mut(target).upper_bounds.push(bound)
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

    /// Imposes an exact bound on a key.  When fully resolved, the types need to match _exactly_.
    pub(crate) fn exact_bound(&mut self, target: TcKey, bound: T) -> Result<(), TcErr<T>> {
        let target_node = self.repr_mut(target);
        if let Some(ref old) = target_node.exact_bound {
            if old != &bound {
                Err(TcErr::ConflictingExactBounds(target, old.clone(), bound))
            } else {
                Ok(())
            }
        } else {
            if let Some(arity) = bound.arity() {
                for i in 0..arity {
                    let child_key = self.nth_child(target, i)?;
                    let child_type = bound.nth_child(i);
                    self.exact_bound(child_key, child_type.clone())?;
                }
            }
            let target_node = self.repr_mut(target); // drop target_node bc of double mut borrow.
            target_node.exact_bound = Some(bound);
            Ok(())
        }
    }

    // INTERNAL HELPER FUNCTIONS

    /// Transforms `sub` into a forward to `repr`.
    fn establish_fwd(&mut self, sub: TcKey, repr: TcKey) -> Result<(), TcErr<T>> {
        if sub == repr {
            // sub and repr are already in the same eq class since we started
            // out with the identity relation;  nothing to do.
            return Ok(());
        }
        let FullVertex { this, ref ty, .. } = *self.repr(sub);
        let repr_v = self.repr(repr);
        let new_ty = repr_v.ty.meet(ty).map_err(|e| TcErr::KeyEquation(this, repr_v.this, e))?;
        assert_eq!(this, sub, "Cannot establish a forward for a vertex that already is a forward.");
        let mut local = Vertex::Fwd { this, repr };
        std::mem::swap(self.vertex_mut(local.this()), &mut local);
        let sub = local.mut_full();
        let mut rep_children = self.repr(repr).children.clone();

        let max_children = usize::max(sub.children.len(), rep_children.len());
        Self::fill_with(&mut sub.children, None, max_children);
        Self::fill_with(&mut rep_children, None, max_children);

        let new_children = rep_children
            .iter()
            .zip(sub.children.iter())
            .map(|(c1, c2)| match (c1, c2) {
                (None, x) | (x, None) => Ok(*x),
                (Some(c1), Some(c2)) => {
                    let v1 = self.repr(*c1).this;
                    let v2 = self.repr(*c2).this;
                    self.equate(v1, v2)?;
                    Ok(Some(self.repr(*c1).this)) // the repr might have changed.
                }
            })
            .collect::<Result<Vec<Option<TcKey>>, TcErr<T>>>()?;

        // Commit changes
        let mut repr_v = self.repr_mut(repr);
        match (&repr_v.exact_bound, &sub.exact_bound) {
            (None, None) | (Some(_), None) => {}
            (None, Some(y)) => {
                let _ = repr_v.exact_bound.replace(y.clone());
            }
            (Some(x), Some(y)) if x == y => {}
            (Some(x), Some(y)) => return Err(TcErr::ConflictingExactBounds(repr_v.this, x.clone(), y.clone())),
        };
        repr_v.upper_bounds.extend(sub.upper_bounds.iter());
        repr_v.children = new_children;
        repr_v.ty = new_ty;
        Ok(())
    }

    /// See `apply_variant`.
    fn resolve_children_for(&mut self, target_key: TcKey) -> Result<bool, TcErr<T>> {
        let target = self.repr_mut(target_key);
        let arity = match target.ty.arity() {
            None => return Ok(false),
            Some(a) => a,
        };
        if target.children.len() > arity {
            return Err(TcErr::ChildAccessOutOfBound(target.this, target.ty.clone(), target.children.len()));
        }
        Self::fill_with(&mut target.children, None, arity);
        let target = self.repr(target_key); // get rid of mutable borrow

        let declared =
            target.children.iter().map(|c| c.map(|vr| self.repr(vr).ty.clone()).unwrap_or_else(T::unconstrained));
        let children: Vec<T> = declared
            .enumerate()
            .map(|(ix, ty)| ty.meet(target.ty.nth_child(ix)))
            .collect::<Result<Vec<T>, T::Err>>()
            .map_err(|e| TcErr::Bound(target.this, None, e))?;
        assert_eq!(arity, children.len());

        let new = target.ty.with_children(children.into_iter());
        if new != target.ty {
            self.repr_mut(target_key).ty = new;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    fn add_vertex(&mut self, vertex: Vertex<T>) {
        self.vertices.push(vertex);
    }

    fn add_explicit_bound(&mut self, target: TcKey, bound: T) -> Result<bool, TcErr<T>> {
        let vertex = self.repr(target);
        let new = vertex.ty.meet(&bound).map_err(|e| TcErr::Bound(target, None, e))?;
        if vertex.ty == new {
            return Ok(false);
        }
        if let Some(arity) = new.arity() {
            for i in 0..arity {
                let child_key = self.nth_child(target, i)?;
                let child_type = bound.nth_child(i);
                self.add_explicit_bound(child_key, child_type.clone())?;
            }
        }
        let vertex = self.repr(target); // Needed to release borrow before.
        match vertex.ty.arity() {
            Some(arity) if arity < vertex.children.len() => {
                Err(TcErr::ChildAccessOutOfBound(target, vertex.ty.clone(), vertex.children.len()))
            }
            _ => Ok(true),
        }
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

impl<T: Abstract> ConstraintGraph<T> {
    /// Starts a fix point computation successively checking and resolving constraints captured in the graph.  
    /// Returns the type table mapping each registered key to a type if no contradiction occurs.
    pub(crate) fn solve(mut self) -> Result<HashMap<TcKey, T>, TcErr<T>> {
        let mut change = true;
        while change {
            change = false;
            change |= self.resolve_asymmetric()?;
            change |= self.resolve_children()?;
        }
        if let Some(v) = self.reprs().find(|v| v.exact_bound.as_ref().map(|bound| bound != &v.ty).unwrap_or(false)) {
            return Err(TcErr::ExactTypeViolation(v.this, v.ty.clone(), v.exact_bound.clone()));
        }
        let res = self
            .vertices
            .iter()
            .map(|v| v.this())
            .collect::<Vec<TcKey>>()
            .into_iter()
            .map(|k| (k, self.repr(k).ty.clone()))
            .collect();
        Ok(res)
    }

    /// Meets all the types of upper bounds with the type of the vertex itself.
    fn resolve_asymmetric(&mut self) -> Result<bool, TcErr<T>> {
        self.vertices
            .iter()
            .map(Vertex::this)
            .collect::<Vec<TcKey>>()
            .into_iter()
            .map(|vr| {
                let vertex = self.repr(vr);
                let new = vertex
                    .upper_bounds
                    .iter()
                    .map(|vr| {
                        let v = &self.repr(*vr);
                        (&v.ty, v.this)
                    })
                    .fold(Ok(vertex.ty.clone()), |a, (ty, key)| {
                        a.and_then(|a| a.meet(ty).map_err(|e| TcErr::Bound(vertex.this, Some(key), e)))
                    })?;
                let change = vertex.ty != new;
                if change {
                    self.repr_mut(vr).ty = new;
                }
                Ok(change)
            })
            .fold(Ok(false), |a, b| a.and_then(|a| b.map(|b| a || b)))
    }

    /// Checks and applies all constraints entailed by children and variant relations.
    fn resolve_children(&mut self) -> Result<bool, TcErr<T>> {
        self.reprs()
            .map(|v| v.this)
            .collect::<Vec<TcKey>>()
            .into_iter()
            .map(|vref| self.resolve_children_for(vref))
            .fold(Ok(false), |a, b| a.and_then(|a| b.map(|b| a || b)))
    }
}

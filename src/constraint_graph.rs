use crate::{Abstract, TcErr, TcKey};
use std::collections::HashMap;

#[derive(Debug, Clone)]
pub(crate) struct ConstraintGraph<T: Abstract> {
    vertices: Vec<Vertex<T>>,
    key_map: HashMap<TcKey, VertexRef>,
}

type VertexRef = usize;

#[derive(Debug, Clone)]
enum Vertex<T: Abstract> {
    Fwd { key: TcKey, this: VertexRef, repr: VertexRef },
    Repr(FullVertex<T>),
}

impl<T: Abstract> Vertex<T> {
    fn key(&self) -> TcKey {
        match self {
            Vertex::Fwd { key, .. } => *key,
            Vertex::Repr(fv) => fv.key,
        }
    }

    fn this(&self) -> VertexRef {
        match self {
            Vertex::Fwd { this, .. } => *this,
            Vertex::Repr(fv) => fv.this,
        }
    }

    fn mut_full(&mut self) -> &mut FullVertex<T> {
        match self {
            Vertex::Fwd { .. } => panic!("That's not a rep!!"),
            Vertex::Repr(vf) => vf,
        }
    }

    /// Returns the reference of the vertex representing this one.  Returns None if this vertex represents itself.
    fn get_repr(&self) -> Option<VertexRef> {
        match self {
            Vertex::Fwd { repr, .. } => Some(*repr),
            Vertex::Repr(_) => None,
        }
    }
}

#[derive(Debug, Clone)]
struct FullVertex<T: Abstract> {
    children: Vec<Option<VertexRef>>,
    upper_bounds: Vec<VertexRef>,
    this: VertexRef,
    key: TcKey,
    ty: T,
}

impl<T: Abstract> Vertex<T> {
    fn new_niladic(key: TcKey, this: VertexRef) -> Vertex<T> {
        Vertex::Repr(FullVertex { children: Vec::new(), upper_bounds: Vec::new(), this, key, ty: T::unconstrained() })
    }
}

impl<T: Abstract> ConstraintGraph<T> {
    pub(crate) fn new() -> ConstraintGraph<T> {
        ConstraintGraph { vertices: Vec::new(), key_map: HashMap::new() }
    }

    pub(crate) fn add(&mut self, key: TcKey) {
        let r = self.next_ref();
        let v = Vertex::new_niladic(key, r);
        self.add_vertex(key, v);
    }

    pub(crate) fn register_variant(&mut self, target: TcKey, variant: T::VariantTag) -> Result<(), TcErr<T>> {
        self.apply_variant(target, variant).map(|_| ())
    }

    /// TODO:  This function is incredibly ugly.
    pub(crate) fn nth_child<F>(&mut self, parent: TcKey, nth: usize, keygen: F) -> Result<TcKey, TcErr<T>>
    where
        F: FnOnce() -> TcKey,
    {
        let parent_v = self.repr_mut_from_key(parent);
        if parent_v.ty.arity().map(|ar| ar < nth).unwrap_or(false) {
            return Err(TcErr::ChildAccessOutOfBound(parent_v.ty.variant().unwrap(), nth));
        }
        Self::fill_with(&mut parent_v.children, None, nth);
        let nth_child = parent_v.children[nth];
        drop(parent_v);
        if let Some(child) = nth_child {
            return Ok(self.vertices[child].key().clone());
        }
        let key = keygen();
        self.add(key);
        let vertex = self.vertex(key).this();
        self.repr_mut_from_key(parent).children[nth] = Some(vertex);
        Ok(key)
    }

    pub(crate) fn add_upper_bound(&mut self, target: TcKey, bound: TcKey) {
        let bound = self.repr_from_key(bound).this;
        self.repr_mut_from_key(target).upper_bounds.push(bound)
    }

    pub(crate) fn equate(&mut self, left: TcKey, right: TcKey) {
        let left = self.repr_from_key(left).this;
        let right = self.repr_from_key(right).this;
        let (rep, sub) = if left < right { (left, right) } else { (right, left) };
        self.establish_fwd(sub, rep);
    }

    pub(crate) fn explicit_bound(&mut self, target: TcKey, bound: T) -> Result<(), TcErr<T>> {
        self.add_explicit_bound(target, bound).map(|_| ())
    }

    // INTERNAL HELPER FUNCTIONS

    fn establish_fwd(&mut self, sub: VertexRef, repr: VertexRef) {
        let FullVertex { this, key, .. } = *self.repr(sub);
        assert_eq!(this, sub, "Cannot establish a forward for a vertex that already is a forward.");
        let mut local = Vertex::Fwd { key, this, repr };
        std::mem::swap(&mut self.vertices[local.this()], &mut local);
        let sub = local.mut_full();
        let mut rep_children = self.repr(repr).children.clone();

        let max_children = usize::max(sub.children.len(), rep_children.len());
        Self::fill_with(&mut sub.children, None, max_children);
        Self::fill_with(&mut rep_children, None, max_children);

        let new_children = rep_children
            .iter()
            .zip(sub.children.iter())
            .map(|(c1, c2)| match (c1, c2) {
                (None, x) | (x, None) => *x,
                (Some(c1), Some(c2)) => {
                    let v1 = self.repr(*c1).key;
                    let v2 = self.repr(*c2).key;
                    self.equate(v1, v2);
                    Some(self.repr(*c1).this) // the repr might have changed.
                }
            })
            .collect();

        // Commit changes
        let mut rep_v = self.repr_mut(repr);
        rep_v.upper_bounds.extend(sub.upper_bounds.iter());
        rep_v.children = new_children;
    }

    fn apply_variant(&mut self, target: TcKey, variant: T::VariantTag) -> Result<bool, TcErr<T>> {
        let v = self.repr_mut_from_key(target);
        if let Some(old) = v.ty.variant() {
            if old != variant {
                return Err(TcErr::DoubleVariantAssignment(target, old, variant));
            }
        }
        let target_ref = v.this;
        drop(v);
        self.meet_variant_type(target_ref, variant)
    }

    fn meet_variant_type(&mut self, target_ref: VertexRef, variant: T::VariantTag) -> Result<bool, TcErr<T>> {
        let v = self.repr(target_ref);
        let target_key = v.key;
        let target_ty = v.ty.clone();
        let mut children = v.children.clone();
        if children.len() > T::variant_arity(variant) {
            return Err(TcErr::ChildAccessOutOfBound(variant, children.len()));
        }
        Self::fill_with(&mut children, None, T::variant_arity(variant));
        drop(v);
        let children_types =
            children.into_iter().map(|c| c.map(|vr| self.repr(vr).ty.clone()).unwrap_or(T::unconstrained())).collect();
        let registered_ty = T::from_tag(variant, children_types);
        let new_ty = target_ty.meet(registered_ty).map_err(|e| TcErr::TypeBound(target_key, e))?;
        let change = self.repr(target_ref).ty != new_ty;
        self.repr_mut(target_ref).ty = new_ty;
        Ok(change)
    }

    fn add_vertex(&mut self, key: TcKey, vertex: Vertex<T>) {
        let r = vertex.this();
        assert!(r == self.vertices.len());
        self.vertices.push(vertex);
        self.key_map.insert(key, r);
    }

    fn add_explicit_bound(&mut self, target: TcKey, bound: T) -> Result<bool, TcErr<T>> {
        let mut vertex = self.repr_mut_from_key(target);
        match vertex.ty.clone().meet(bound) {
            Ok(new) => {
                let change = vertex.ty != new;
                vertex.ty = new;
                Ok(change)
            }
            Err(e) => Err(TcErr::TypeBound(target, e)),
        }
    }

    // ACCESS LOGIC

    pub(crate) fn peek(&self, key: TcKey) -> &T {
        &self.repr_from_key(key).ty
    }

    fn next_ref(&self) -> VertexRef {
        self.vertices.len()
    }

    fn vertex(&self, key: TcKey) -> &Vertex<T> {
        let vr = self.key_to_ref(key);
        &self.vertices[vr]
    }

    fn repr_mut_from_key(&mut self, key: TcKey) -> &mut FullVertex<T> {
        self.repr_mut(self.key_to_ref(key))
    }

    fn repr_from_key(&self, key: TcKey) -> &FullVertex<T> {
        self.repr(self.key_to_ref(key))
    }

    fn repr_mut(&mut self, v: VertexRef) -> &mut FullVertex<T> {
        match self.vertices[v].get_repr() {
            Some(next) => self.repr_mut(next),
            None => self.vertices[v].mut_full(),
        }
    }

    fn reprs(&self) -> Vec<VertexRef> {
        self.vertices
            .iter()
            .filter_map(|v| match v {
                Vertex::Fwd { .. } => None,
                Vertex::Repr(fv) => Some(fv.this),
            })
            .collect()
    }

    fn repr(&self, v: VertexRef) -> &FullVertex<T> {
        match &self.vertices[v] {
            Vertex::Repr(fv) => fv,
            Vertex::Fwd { repr, .. } => self.repr(*repr),
        }
    }

    fn key_to_ref(&self, key: TcKey) -> VertexRef {
        *self.key_map.get(&key).unwrap()
    }

    fn fill_with<X: Clone>(v: &mut Vec<X>, entry: X, size: usize) {
        v.extend(vec![entry; v.len() - size]);
    }
}

impl<T: Abstract> ConstraintGraph<T> {
    pub(crate) fn solve(mut self) -> Result<HashMap<TcKey, T>, TcErr<T>> {
        let mut change = true;
        while change {
            change = false;
            change |= self.resolve_asymmetric()?;
            change |= self.resolve_children()?;
        }
        let res = self
            .vertices
            .iter()
            .map(|v| v.key())
            .collect::<Vec<TcKey>>()
            .into_iter()
            .map(|k| (k, self.repr_from_key(k).ty.clone()))
            .collect();
        Ok(res)
    }

    /// Meets all the types of upper bounds with the type of the vertex itself.
    fn resolve_asymmetric(&mut self) -> Result<bool, TcErr<T>> {
        self.vertices
            .iter()
            .map(Vertex::this)
            .collect::<Vec<VertexRef>>()
            .into_iter()
            .map(|vr| {
                let vertex = self.repr(vr);
                let old = vertex.ty.clone();
                let new = vertex
                    .upper_bounds
                    .iter()
                    .map(|vr| self.repr(*vr).ty.clone())
                    .fold(Ok(old.clone()), |a, b| a.and_then(|a| a.meet(b)))
                    .map_err(|e| TcErr::TypeBound(vertex.key, e))?;
                drop(vertex);
                let change = old != new;
                if change {
                    self.repr_mut(vr).ty = new;
                }
                Ok(change)
            })
            .fold(Ok(false), |a, b| a.and_then(|a| b.map(|b| a || b)))
    }

    fn resolve_children(&mut self) -> Result<bool, TcErr<T>> {
        self.reprs()
            .into_iter()
            .map(|rep| {
                if let Some(variant) = self.repr(rep).ty.variant() {
                    self.meet_variant_type(rep, variant)
                } else {
                    Ok(false)
                }
            })
            .fold(Ok(false), |a, b| a.and_then(|a| b.map(|b| a || b)))
    }
}

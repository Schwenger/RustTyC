use crate::{ContextType, Key, TcErr};

use super::{inferred::Inferred, ConstraintGraph};

#[derive(Debug, Clone)]
pub(crate) enum Vertex<T: ContextType> {
    /// Represents a former vertex that was unified with another one and not chosen to be the representative.
    Fwd { this: Key, repr: Key },
    /// Represents a full vertex.
    Repr(FullVertex<T>),
}

impl<T: ContextType> Vertex<T> {
    pub(crate) fn this(&self) -> Key {
        match self {
            Vertex::Fwd { this, .. } => *this,
            Vertex::Repr(fv) => fv.this,
        }
    }

    /// Grants mutable access to the underlying full vertex.
    /// # Panics
    /// Panics if `self` is not a full vertex.
    pub(crate) fn mut_full(&mut self) -> &mut FullVertex<T> {
        match self {
            Vertex::Fwd { .. } => panic!("That's not a rep!!"),
            Vertex::Repr(vf) => vf,
        }
    }

    /// Grants immutable access to the underlying full vertex.
    /// # Panics
    /// Panics if `self` is not a full vertex.
    pub(crate) fn full(&self) -> &FullVertex<T> {
        match self {
            Vertex::Fwd { .. } => panic!("That's not a rep!!"),
            Vertex::Repr(vf) => vf,
        }
    }

    /// Returns the reference of the vertex representing this one.  Returns None if this vertex represents itself.
    pub(crate) fn get_repr_nontrans(&self) -> Option<Key> {
        match self {
            Vertex::Fwd { repr, .. } => Some(*repr),
            Vertex::Repr(_) => None,
        }
    }
    /// Creates a full vertex without information regarding its children.
    pub(crate) fn new_niladic(this: Key) -> Vertex<T> {
        Vertex::Repr(FullVertex { this, ty: Inferred::top() })
    }
}

#[derive(Debug, Clone)]
pub(crate) struct FullVertex<T: ContextType> {
    pub(crate) this: Key,
    pub(crate) ty: Inferred<T>,
}

impl<T: ContextType> ConstraintGraph<T> {
    /// Transforms `sub` into a forward to `repr`.
    pub(crate) fn establish_fwd(&mut self, sub: Key, repr: Key, context: &T::Context) -> Result<(), TcErr<T>> {
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

        let equates = repr_v.ty.meet(repr, sub, &sub_v.ty, context)?;
        // Meet-Alternative: let (new_ty, equates) = repr_v.ty.meet(repr, &sub_v.ty)?;
        equates.into_iter().try_for_each(|(a, b)| self.equate(a, b, context))?;

        // Meet-Alternative: self.repr_mut(repr).ty = new_ty;
        Ok(())
    }

    // ACCESS LOGIC
    pub(crate) fn vertex(vertices: &[Vertex<T>], key: Key) -> &Vertex<T> {
        &vertices[key.ix]
    }

    pub(crate) fn vertex_mut(vertices: &mut [Vertex<T>], key: Key) -> &mut Vertex<T> {
        &mut vertices[key.ix]
    }

    pub(crate) fn repr_mut(vertices: &mut Vec<Vertex<T>>, v: Key) -> &mut FullVertex<T> {
        match Self::vertex(vertices, v).get_repr_nontrans() {
            Some(next) => Self::repr_mut(vertices, next),
            None => Self::vertex_mut(vertices, v).mut_full(),
        }
    }

    /// Returns an Iterator over all full vertices in `self`.  This does not resolve forwards, thus every representative only occurs once.
    pub(crate) fn reprs(&self) -> impl Iterator<Item = &FullVertex<T>> {
        self.vertices.iter().filter_map(|v| match v {
            Vertex::Fwd { .. } => None,
            Vertex::Repr(fv) => Some(fv),
        })
    }

    pub(crate) fn repr(&self, v: Key) -> &FullVertex<T> {
        match &Self::vertex(&self.vertices, v) {
            Vertex::Repr(fv) => fv,
            Vertex::Fwd { repr, .. } => self.repr(*repr),
        }
    }
}

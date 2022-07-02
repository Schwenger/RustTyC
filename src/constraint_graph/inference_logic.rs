use crate::{subtys::Equates, ContextType, Key, TcErr};

use super::{graph_logic::Vertex, inferred::Inferred, ConstraintGraph};

impl<T: ContextType> ConstraintGraph<T> {
    /// Starts a fix point computation successively checking and resolving constraints captured in the graph.  
    /// Returns the type table mapping each registered key to a type if no contradiction occurs.
    pub(crate) fn solve_constraints(&mut self, context: T::Context) -> Result<(), TcErr<T>> {
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

    /// Meets all the types of upper bounds with the type of the vertex itself.
    fn resolve_asymmetric(&mut self, context: &T::Context) -> Result<bool, TcErr<T>> {
        self.vertices
            .iter()
            .map(Vertex::this)
            .collect::<Vec<Key>>()
            .into_iter()
            .map(|key| {
                let vertex = self.repr(key);
                let initial: (Inferred<T>, Equates) = (vertex.ty.clone(), Vec::new());
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
                let change = !Inferred::equal(&vertex.ty, &new_type, context);
                Self::repr_mut(&mut self.vertices, key).ty = new_type;
                equates.into_iter().try_for_each(|(k1, k2)| self.equate(k1, k2, context))?;
                Ok(change)
            })
            .collect::<Result<Vec<bool>, TcErr<T>>>()
            .map(|changes| changes.into_iter().any(|b| b))
    }

    pub(crate) fn add_explicit_bound(&mut self, target: Key, bound: T, context: &T::Context) -> Result<(), TcErr<T>> {
        let target_v = Self::repr_mut(&mut self.vertices, target);
        target_v.ty.with_bound(target, bound, context)
    }
}

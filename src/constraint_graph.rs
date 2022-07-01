use crate::children::{ChildAccessor, Children, ReqsMerge};
use crate::type_table::{Constructable, PreliminaryTypeTable, TypeTable};
use crate::{types::ContextType, Key, TcErr};

mod construction_logic;
mod graph_logic;
mod inference_logic;
mod type_info;
use graph_logic::Vertex;

use self::graph_logic::FullVertex;

#[derive(Debug, Clone)]
pub(crate) struct ConstraintGraph<T: ContextType> {
    vertices: Vec<Vertex<T>>,
}

impl<T: ContextType> ConstraintGraph<T> {
    /// Creates an empty constraint graph.
    pub(crate) fn new() -> Self {
        ConstraintGraph { vertices: Vec::new() }
    }

    /// Create an iterator over all keys currently registered in the graph.
    pub(crate) fn all_keys(&self) -> impl Iterator<Item = Key> + '_ {
        self.vertices.iter().map(|v| v.this())
    }

    /// Creates and registers a new vertex.
    pub(crate) fn create_vertex(&mut self) -> Key {
        self.new_vertex().this()
    }

    pub(crate) fn lift(&mut self, variant: T, children: Children) -> Key {
        let v = self.new_vertex().mut_full();
        v.ty.ty = variant;
        v.ty.children = children;
        v.this
    }

    /// Registers that a key has at least this child.  If this fact was already known and thus a key is already associated with the child,
    /// the key is returned without calling the `keygen` function.  Otherwise, `keygen` generates a new key which will be added to the graph regularly,
    /// associated with the child, and returned.
    /// If the addition of the child reveals a contradiction, an Err is returned.  An Ok does _not_ indicate the absence of a contradiction.
    pub(crate) fn impose_child(&mut self, parent: Key, child: ChildAccessor) -> Result<Key, TcErr<T>> {
        {
            let parent_v = Self::repr_mut(&mut self.vertices, parent);
            if let Some(child_key) = parent_v.ty.child(parent, &child)? {
                return Ok(child_key);
            }
        }
        let child_key = self.create_vertex();
        let parent_v = Self::repr_mut(&mut self.vertices, parent);
        let merge = parent_v.ty.add_child(parent, &child, child_key)?;
        assert!(merge == ReqsMerge::No);
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
}

impl<T: ContextType> ConstraintGraph<T> {
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

    fn new_vertex(&mut self) -> &mut Vertex<T> {
        let key = Key::new(self.vertices.len());
        let v = Vertex::new_niladic(key);
        self.vertices.push(v);
        self.vertices.last_mut().unwrap() // we just pushed it onto the vec.
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

    pub(crate) fn solve_preliminary(mut self, context: T::Context) -> Result<PreliminaryTypeTable<T>, TcErr<T>> {
        self.solve_constraints(context)?;
        Ok(self.construct_preliminary())
    }
}

use std::collections::HashMap;

use crate::types::UpperBoundedType;
use crate::{
    type_table::{Constructable, Preliminary, PreliminaryTypeTable, ResolvedChildren, TypeTable},
    Key, TcErr,
};

use super::{graph_logic::FullVertex, ConstraintGraph};

impl<T> ConstraintGraph<T>
where
    T: Constructable,
{
    pub(crate) fn construct_preliminary(self) -> PreliminaryTypeTable<T> {
        self.vertices
            .iter()
            .map(|v| v.this())
            .collect::<Vec<Key>>()
            .into_iter()
            .map(|key| (key, self.prelim_for(key)))
            .collect()
    }

    fn prelim_for(&self, key: Key) -> Preliminary<T> {
        self.repr(key).ty.clone().into_preliminary()
    }

    fn unresolved_type() -> <T as Constructable>::Type {
        T::Type::top()
    }

    // TODO: Refactor
    pub(crate) fn construct_types(self) -> Result<TypeTable<T>, TcErr<T>> {
        let mut resolved: HashMap<Key, T::Type> = HashMap::new();
        let mut open: Vec<&FullVertex<T>> = self.reprs().collect();
        loop {
            let mut still_open = Vec::with_capacity(open.len());
            let num_open = open.len();
            for v in open {
                let children = v.ty.children.clone();
                if children.is_none() {
                    let ty =
                        v.ty.ty
                            .construct(ResolvedChildren::None)
                            .map_err(|e| TcErr::Construction(v.this, v.ty.clone().into_preliminary(), e))?;
                    let _ = resolved.insert(v.this, ty);
                } else {
                    let mut resolved_children = Vec::new();
                    for (_child, key) in children.to_vec() {
                        let constructed = if let Some(key) = key {
                            resolved.get(&self.repr(*key).this).cloned()
                        } else {
                            Some(Self::unresolved_type())
                        };
                        resolved_children.push(constructed);
                    }
                    if resolved_children.iter().all(Option::is_some) {
                        let children = if children.all_field() {
                            debug_assert_eq!(resolved_children.iter().flatten().count(), children.to_vec().len());
                            let children_map = children
                                .to_vec()
                                .into_iter()
                                .map(|(child, _)| child.field().unwrap())
                                .zip(resolved_children.into_iter().flatten())
                                .collect::<HashMap<_, _>>();
                            debug_assert_eq!(children_map.len(), children.to_vec().len());
                            ResolvedChildren::Named(children_map)
                        } else {
                            debug_assert_eq!(resolved_children.iter().flatten().count(), children.to_vec().len());
                            let mut children_map = children
                                .to_vec()
                                .into_iter()
                                .map(|(child, _)| child.index().unwrap())
                                .zip(resolved_children.into_iter().flatten())
                                .collect::<Vec<_>>();
                            children_map.sort_by_key(|(idx, _ty)| *idx);
                            let children_map = children_map.into_iter().map(|(_, ty)| ty).collect::<Vec<_>>();
                            debug_assert_eq!(children_map.len(), children.to_vec().len());
                            ResolvedChildren::Indexed(children_map)
                        };
                        let ty =
                            v.ty.ty
                                .construct(children)
                                .map_err(|e| TcErr::Construction(v.this, v.ty.clone().into_preliminary(), e))?;
                        let _ = resolved.insert(v.this, ty);
                    } else {
                        still_open.push(v)
                    }
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

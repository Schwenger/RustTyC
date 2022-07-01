use std::collections::HashMap;

use crate::types::UpperBoundedType;
use crate::{
    type_table::{Constructable, Preliminary, PreliminaryTypeTable, ResolvedSubTys, TypeTable},
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
                let subtys = v.ty.subtys.clone();
                if subtys.is_none() {
                    let ty =
                        v.ty.ty
                            .construct(ResolvedSubTys::None)
                            .map_err(|e| TcErr::Construction(v.this, v.ty.clone().into_preliminary(), e))?;
                    let _ = resolved.insert(v.this, ty);
                } else {
                    let mut resolved_subtys = Vec::new();
                    for (_subty, key) in subtys.to_vec() {
                        let constructed = if let Some(key) = key {
                            resolved.get(&self.repr(*key).this).cloned()
                        } else {
                            Some(Self::unresolved_type())
                        };
                        resolved_subtys.push(constructed);
                    }
                    if resolved_subtys.iter().all(Option::is_some) {
                        let subtys = if subtys.all_field() {
                            debug_assert_eq!(resolved_subtys.iter().flatten().count(), subtys.to_vec().len());
                            let subtys_map = subtys
                                .to_vec()
                                .into_iter()
                                .map(|(access, _)| access.field().unwrap())
                                .zip(resolved_subtys.into_iter().flatten())
                                .collect::<HashMap<_, _>>();
                            debug_assert_eq!(subtys_map.len(), subtys.to_vec().len());
                            ResolvedSubTys::Fields(subtys_map)
                        } else {
                            debug_assert_eq!(resolved_subtys.iter().flatten().count(), subtys.to_vec().len());
                            let mut subtys_map = subtys
                                .to_vec()
                                .into_iter()
                                .map(|(access, _)| access.numeric().unwrap())
                                .zip(resolved_subtys.into_iter().flatten())
                                .collect::<Vec<_>>();
                            subtys_map.sort_by_key(|(idx, _ty)| *idx);
                            let subtys_map = subtys_map.into_iter().map(|(_, ty)| ty).collect::<Vec<_>>();
                            debug_assert_eq!(subtys_map.len(), subtys.to_vec().len());
                            ResolvedSubTys::Numeric(subtys_map)
                        };
                        let ty =
                            v.ty.ty
                                .construct(subtys)
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

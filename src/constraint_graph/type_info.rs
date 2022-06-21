use std::{collections::{HashSet, HashMap}, iter::FromIterator};

use crate::{ContextType, children::{Children, ChildConstraint, Arity}, Key, TcErr, constraint_graph::{OptEquateObligation, EquateObligation}, Infered, type_table::Preliminary};

use super::ConstraintGraph;


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeInfo<T: ContextType> {
    pub(crate) variant: T,
    pub(crate) children: Children,
    pub(crate) upper_bounds: HashSet<Key>,
}

impl<T: ContextType> TypeInfo<T> {
    pub(crate) fn top() -> Self {
        TypeInfo { variant: T::top(), children: Children::Unknown, upper_bounds: HashSet::new() }
    }

    pub(crate) fn equal(this: &Self, that: &Self, ctx: &T::Context) -> bool {
        T::equal(&this.variant, &that.variant, ctx)
            && this.children == that.children
            && this.upper_bounds == that.upper_bounds
    }

    pub(crate) fn apply_child_constraint_checked(
        &mut self,
        this: Key,
        constraint: ChildConstraint,
        ctx: &T::Context,
        child_ids: &HashMap<String, usize>,
        child_names: &[String],
    ) -> Result<(), TcErr<T>> {
        match (&self.variant.arity(ctx).substitute(child_ids), constraint) {
            (Arity::None, ChildConstraint::Indexed(new_arity)) => {
                return Err(TcErr::ChildAccessOutOfBound(this, self.variant.clone(), new_arity))
            }
            (Arity::None, ChildConstraint::Named(new)) => {
                return Err(TcErr::FieldDoesNotExist(
                    this,
                    self.variant.clone(),
                    new.into_iter().map(|k| child_names[k].clone()).collect(),
                ))
            }
            (Arity::None, ChildConstraint::Unconstrained) | (Arity::None, ChildConstraint::NoChildren) => {
                match &mut self.children {
                    Children::Unknown => self.children = Children::None,
                    Children::None => {}
                    Children::Indexed(_) | Children::Named(_) => {
                        unreachable!("Mismatch between arity type and children")
                    }
                }
            }
            (Arity::FixedIndexed(given_arity), ChildConstraint::Indexed(new_arity)) if new_arity > *given_arity => {
                return Err(TcErr::ChildAccessOutOfBound(this, self.variant.clone(), new_arity))
            }
            (Arity::FixedIndexed(given_arity), ChildConstraint::Indexed(_)) => match &mut self.children {
                Children::Unknown => self.children = Children::Indexed(vec![None; *given_arity]),
                Children::Indexed(children) => ConstraintGraph::<T>::fill_with(children, None, *given_arity),
                Children::Named(_) | Children::None => unreachable!("Mismatch between arity type and children"),
            },
            (Arity::Variable, ChildConstraint::Indexed(new_arity)) => match &mut self.children {
                Children::Unknown => self.children = Children::Indexed(vec![None; new_arity]),
                Children::Indexed(children) => ConstraintGraph::<T>::fill_with(children, None, new_arity),
                Children::Named(_) => {
                    return Err(TcErr::IndexedAccessOnNamedType(this, self.variant.clone(), new_arity));
                }
                Children::None => return Err(TcErr::ChildAccessOutOfBound(this, self.variant.clone(), new_arity)),
            },
            (Arity::FixedNamed(target), ChildConstraint::Named(new)) if !new.is_subset(target) => {
                return Err(TcErr::FieldDoesNotExist(
                    this,
                    self.variant.clone(),
                    new.difference(target).map(|k| child_names[*k].clone()).collect(),
                ))
            }
            (Arity::FixedNamed(target), ChildConstraint::Named(_)) => match &mut self.children {
                Children::Unknown => {
                    self.children = Children::Named(HashMap::from_iter(target.iter().map(|k| (*k, None))))
                }
                Children::Named(names) => {
                    names.extend(target.difference(&names.keys().cloned().collect()).cloned().map(|k| (k, None)))
                }
                Children::Indexed(_) | Children::None => unreachable!("Mismatch between arity kind and children"),
            },
            (Arity::Variable, ChildConstraint::Named(names)) => match &mut self.children {
                Children::Unknown => {
                    self.children = Children::Named(HashMap::from_iter(names.into_iter().map(|k| (k, None))))
                }
                Children::Named(children) => {
                    let current: HashSet<usize> = children.keys().copied().collect();
                    children.extend(names.difference(&current).cloned().map(|k| (k, None)))
                }
                Children::Indexed(_) => {
                    return Err(TcErr::FieldAccessOnIndexedTyped(
                        this,
                        self.variant.clone(),
                        names.iter().map(|k| child_names[*k].clone()).collect(),
                    ));
                }
                Children::None => {
                    return Err(TcErr::FieldDoesNotExist(
                        this,
                        self.variant.clone(),
                        names.iter().map(|k| child_names[*k].clone()).collect(),
                    ))
                }
            },
            (Arity::FixedNamed(_), ChildConstraint::Indexed(idx)) => {
                return Err(TcErr::IndexedAccessOnNamedType(this, self.variant.clone(), idx));
            }
            (Arity::FixedIndexed(_), ChildConstraint::Named(name)) => {
                return Err(TcErr::FieldAccessOnIndexedTyped(
                    this,
                    self.variant.clone(),
                    name.iter().map(|k| child_names[*k].clone()).collect(),
                ));
            }
            (_, ChildConstraint::Unconstrained) | (_, ChildConstraint::NoChildren) => {
                //Nothing to do
            }
        }
        Ok(())
    }

    pub(crate) fn apply_child_constraint_unchecked(&mut self, constraint: ChildConstraint) {
        match constraint {
            ChildConstraint::Indexed(idx) => match &mut self.children {
                Children::Unknown => self.children = Children::Indexed(vec![None; idx]),
                Children::Indexed(children) => ConstraintGraph::<T>::fill_with(children, None, idx),
                Children::Named(_) | Children::None => unreachable!("Mismatch between arity type and children"),
            },
            ChildConstraint::Named(target) => match &mut self.children {
                Children::Unknown => {
                    self.children = Children::Named(HashMap::from_iter(target.iter().map(|k| (*k, None))))
                }
                Children::Named(names) => {
                    names.extend(target.difference(&names.keys().cloned().collect()).cloned().map(|k| (k, None)))
                }
                Children::Indexed(_) | Children::None => unreachable!("Mismatch between arity kind and children"),
            },
            ChildConstraint::Unconstrained | ChildConstraint::NoChildren => {
                // Nothing to do
            }
        }
    }

    pub(crate) fn child_indexed(&self, idx: usize) -> Option<Key> {
        debug_assert!(self.children.is_indexed());
        debug_assert!(self.children.len().unwrap_or(0) > idx);
        self.children.indexed().unwrap()[idx]
    }

    pub(crate) fn child_named(&self, id: usize) -> Option<Key> {
        debug_assert!(self.children.is_named());
        debug_assert!(self.children.named().unwrap().contains_key(&id));
        self.children.named().unwrap()[&id]
    }

    pub(crate) fn set_child_indexed(&mut self, n: usize, child: Key) {
        debug_assert!(self.children.is_indexed());
        debug_assert!(self.children.len().unwrap_or(0) > n);
        self.children.indexed_mut().unwrap()[n] = Some(child);
    }

    pub(crate) fn set_child_named(&mut self, id: usize, child: Key) {
        debug_assert!(self.children.is_named());
        debug_assert!(self.children.named().unwrap().contains_key(&id));
        let _ = self.children.named_mut().unwrap().insert(id, Some(child));
    }

    pub(crate) fn add_upper_bound(&mut self, bound: Key) {
        let _ = self.upper_bounds.insert(bound);
    }

    pub(crate) fn meet(
        &mut self,
        this: Key,
        target_key: Key,
        rhs: &Self,
        ctx: &T::Context,
        child_ids: &HashMap<String, usize>,
        child_names: &[String],
    ) -> Result<EquateObligation, TcErr<T>> {
        // TODO: Extremely inefficient; improve.
        let lhs = self;
        let mut is_indexed = true;
        let mut unknown_children = false;
        let mut no_children = false;

        // println!("Meeting: {:?} and {:?}", lhs, rhs);

        match (&lhs.children, &rhs.children) {
            (Children::Indexed(_), Children::Named(_)) | (Children::Named(_), Children::Indexed(_)) => {
                return Err(TcErr::ChildKindMismatch(this, lhs.variant.clone(), target_key, rhs.variant.clone()))
            }
            (Children::Unknown, Children::Indexed(rhs_c)) => {
                debug_assert!(rhs.variant.arity(ctx).to_opt().map(|a| a == rhs_c.len()).unwrap_or(true));
            }
            (Children::Indexed(lhs_c), Children::Unknown) => {
                debug_assert!(lhs.variant.arity(ctx).to_opt().map(|a| a == lhs_c.len()).unwrap_or(true));
            }
            (Children::Indexed(lhs_c), Children::Indexed(rhs_c)) => {
                debug_assert!(lhs.variant.arity(ctx).to_opt().map(|a| a == lhs_c.len()).unwrap_or(true));
                debug_assert!(rhs.variant.arity(ctx).to_opt().map(|a| a == rhs_c.len()).unwrap_or(true));
            }
            (Children::Named(children), Children::Unknown) => {
                is_indexed = false;

                #[cfg(debug_assertions)]
                {
                    match lhs.variant.arity(ctx).substitute(child_ids) {
                        Arity::FixedNamed(lhs_names) => {
                            debug_assert!(children.keys().copied().collect::<HashSet<_>>() == lhs_names);
                        }
                        _ => {
                            unreachable!("Mismatch between Children and arity")
                        }
                    }
                }
            }
            (Children::Unknown, Children::Named(children)) => {
                is_indexed = false;

                #[cfg(debug_assertions)]
                {
                    match rhs.variant.arity(ctx).substitute(child_ids) {
                        Arity::FixedNamed(rhs_names) => {
                            debug_assert!(children.keys().copied().collect::<HashSet<_>>() == rhs_names);
                        }
                        _ => {
                            unreachable!("Mismatch between Children and arity")
                        }
                    }
                }
            }
            (Children::Named(lhs_c), Children::Named(rhs_c)) => {
                is_indexed = false;

                #[cfg(debug_assertions)]
                {
                    match (lhs.variant.arity(ctx).substitute(child_ids), rhs.variant.arity(ctx).substitute(child_ids)) {
                        (Arity::FixedNamed(lhs_names), Arity::FixedNamed(rhs_names)) => {
                            debug_assert!(lhs_c.keys().copied().collect::<HashSet<_>>() == lhs_names);
                            debug_assert!(rhs_c.keys().copied().collect::<HashSet<_>>() == rhs_names);
                        }
                        _ => {
                            unreachable!("Mismatch between Children and arity")
                        }
                    }
                }
            }
            (Children::Unknown, Children::Unknown) => {
                unknown_children = true;
            }
            (Children::Unknown, Children::None)
            | (Children::None, Children::Unknown)
            | (Children::None, Children::None) => {
                no_children = true;
            }
            (Children::None, _) | (_, Children::None) => {
                return Err(TcErr::ChildKindMismatch(this, lhs.variant.clone(), target_key, rhs.variant.clone()))
            }
        }

        let left = Infered { variant: lhs.variant.clone(), children: lhs.children.to_constraint() };
        let right = Infered { variant: rhs.variant.clone(), children: rhs.children.to_constraint() };
        let Infered { variant: new_variant, children: new_constraint } =
            ContextType::meet(left, right, ctx).map_err(|e| TcErr::Bound(this, Some(target_key), e))?;

        let (mut equates, new_children): (OptEquateObligation, Children) = if unknown_children {
            (vec![], Children::Unknown)
        } else if no_children {
            (vec![], Children::None)
        } else if is_indexed {
            // Make child arrays same length.
            ConstraintGraph::<T>::fill_with(
                lhs.children.indexed_mut().expect("children to be indexed"),
                None,
                rhs.children.len().unwrap_or(0),
            ); // Will be checked later.
            let (equates, new_children) = lhs
                .children
                .indexed()
                .unwrap_or(&vec![])
                .iter()
                .zip(rhs.children.indexed().unwrap_or(&vec![]).iter().chain(std::iter::repeat(&None)))
                .map(|(a, b)| ((*a).zip(*b), (*a).or(*b)))
                .unzip();
            (equates, Children::Indexed(new_children))
        } else {
            let empty_map = HashMap::new();
            let children_l = lhs.children.named().unwrap_or(&empty_map);
            let children_r = rhs.children.named().unwrap_or(&empty_map);
            let (equates, new_children) = children_l
                .keys()
                .chain(children_r.keys())
                .map(|k| {
                    (
                        children_l.get(k).cloned().flatten().zip(children_r.get(k).cloned().flatten()),
                        (*k, children_l.get(k).cloned().flatten().or_else(|| children_r.get(k).cloned().flatten())),
                    )
                })
                .unzip();
            (equates, Children::Named(new_children))
        };

        let equates: EquateObligation = equates.drain(..).flatten().collect();

        // commit changes
        lhs.variant = new_variant;
        lhs.children = new_children;
        lhs.upper_bounds.extend(rhs.upper_bounds.iter());
        lhs.apply_child_constraint_checked(target_key, new_constraint, ctx, child_ids, child_names)?;

        // println!("Result: {:?}", lhs);

        debug_assert!(lhs.variant.arity(ctx).to_opt().map(|a| a == lhs.children.len().unwrap_or(0)).unwrap_or(true));

        Ok(equates)
    }

    pub(crate) fn to_infered(&self) -> Infered<T> {
        Infered { variant: self.variant.clone(), children: self.children.to_constraint() }
    }

    pub(crate) fn with_infered(
        &mut self,
        this: Key,
        p: Infered<T>,
        ctx: &T::Context,
        child_ids: &HashMap<String, usize>,
        child_names: &[String],
    ) -> Result<(), TcErr<T>> {
        let Infered { variant, children: constraint } = p;
        match variant.arity(ctx).substitute(child_ids) {
            Arity::Variable => {
                self.variant = variant;
                self.apply_child_constraint_unchecked(constraint); // set_arity increases or is no-op.
                Ok(())
            }
            Arity::None => {
                assert!(matches!(constraint, ChildConstraint::NoChildren));
                if self.children.len().unwrap_or(0) > 0 {
                    return Err(TcErr::ArityMismatch {
                        key: this,
                        variant,
                        inferred_arity: self.children.len().unwrap_or(0),
                        reported_arity: 0,
                    });
                }
                self.variant = variant;
                // self.apply_child_constraint_unchecked(constraint); // set_arity increases or is no-op.
                debug_assert!(self
                    .variant
                    .arity(ctx)
                    .to_opt()
                    .map(|a| a == self.children.len().unwrap_or(0))
                    .unwrap_or(true));
                Ok(())
            }
            Arity::FixedIndexed(arity) => {
                assert_eq!(
                    arity,
                    constraint.len(),
                    "meet of two variants yielded fixed-arity variant that did not match least arity."
                );
                if self.children.len().unwrap_or(0) > arity {
                    return Err(TcErr::ArityMismatch {
                        key: this,
                        variant,
                        inferred_arity: self.children.len().unwrap_or(0),
                        reported_arity: arity,
                    });
                }
                self.variant = variant;
                self.apply_child_constraint_unchecked(constraint); // set_arity increases or is no-op.
                debug_assert!(self
                    .variant
                    .arity(ctx)
                    .to_opt()
                    .map(|a| a == self.children.len().unwrap_or(0))
                    .unwrap_or(true));
                Ok(())
            }
            Arity::FixedNamed(names) => {
                assert_eq!(
                    &names,
                    constraint.names(),
                    "meet of two variants yielded fixed-named variant that did not match required named."
                );
                let keys = self.children.named().map(|m| m.keys().copied().collect()).unwrap_or_else(HashSet::new);

                if !keys.is_subset(&names) {
                    return Err(TcErr::FieldMismatch {
                        key: this,
                        variant,
                        inferred_fields: keys.iter().map(|k| child_names[*k].clone()).collect(),
                        reported_fields: names.iter().map(|k| child_names[*k].clone()).collect(),
                    });
                }
                self.variant = variant;
                self.apply_child_constraint_unchecked(constraint); // set_arity increases or is no-op.
                debug_assert!(self
                    .variant
                    .arity(ctx)
                    .to_opt()
                    .map(|a| a == self.children.len().unwrap_or(0))
                    .unwrap_or(true));
                Ok(())
            }
        }
    }

    pub(crate) fn to_preliminary(&self) -> Preliminary<T> {
        Preliminary { ty: self.variant.clone(), children: self.children.clone() }
    }
}
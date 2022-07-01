use std::collections::HashSet;

use crate::{ContextType, children::{Children, ChildAccessor, ChildAccessErr, ReqsMerge, Equates}, Key, TcErr, type_table::Preliminary};


#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeInfo<T: ContextType> {
    pub(crate) ty: T,
    pub(crate) children: Children,
    pub(crate) upper_bounds: HashSet<Key>,
}

impl<T: ContextType> TypeInfo<T> {
    pub(crate) fn top() -> Self {
        TypeInfo { ty: T::top(), children: Children::top(), upper_bounds: HashSet::new() }
    }

    pub(crate) fn equal(this: &Self, that: &Self, ctx: &T::Context) -> bool {
        T::equal(&this.ty, &that.ty, ctx)
            && this.children == that.children
            && this.upper_bounds == that.upper_bounds
    }

    pub(crate) fn transform_err(key: Key, ty: &T, err: ChildAccessErr) -> TcErr<T> {
        TcErr::InvalidChildAccessInfered(key, ty.clone(), err.children, err.accessor)
    }

    pub(crate) fn child(&self, this: Key, child: &ChildAccessor) -> Result<Option<Key>, TcErr<T>> {
        self.children.child(child)
            .map_err(|err| Self::transform_err(this, &self.ty, err))
    }

    pub(crate) fn add_child(&mut self, this: Key, child: &ChildAccessor, child_key: Key) -> Result<ReqsMerge, TcErr<T>> {
        self.children.add_child(child, child_key)
            .map_err(|err| Self::transform_err(this, &self.ty, err))
    }

    pub(crate) fn add_upper_bound(&mut self, bound: Key) {
        let _ = self.upper_bounds.insert(bound);
    }

    fn combine_children(&self, this: Key, left: &Children, right: &Children) -> Result<(Children, Equates), TcErr<T>> {
        let mut new_children = Children::empty();

        let all_children = left.to_vec().into_iter()
            .chain(right.to_vec().into_iter());
        let required_equates = all_children.map(|(access, child_key)| {
                new_children.add_potential_child(access, *child_key)
                .map(|merge| merge.zip(*child_key))
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|err| Self::transform_err(this, &self.ty, err))?
            .drain(..)
            .flatten()
            .collect::<Vec<_>>();
        Ok((new_children, required_equates))
    }

    pub(crate) fn meet(
        &mut self,
        this: Key,
        that: Key,
        rhs: &Self,
        ctx: &T::Context,
    ) -> Result<Equates, TcErr<T>> {
        let lhs = self;
        
        let (new_children, mut required_equates) = lhs.combine_children(this, &lhs.children, &rhs.children)?;

        #[cfg(Debug)]
        {
            let new_arity = Self::meet_arity(lhs.ty.arity(ctx), this, rhs.ty.arity(ctx), that)?;
            let debug_children = new_children.impose(new_arity);
            assert!(debug_children.is_ok() && debug_children.unwrap() == new_children);
        }

        let new_ty =
            ContextType::meet(lhs.ty.clone(), rhs.ty.clone(), ctx).map_err(|e| 
                TcErr::IncompatibleTypes {
                    key1: this,
                    ty1: lhs.ty.clone(),
                    key2: that,
                    ty2: rhs.ty.clone(),
                    err: e,
                })?;
        
        let (new_children, mut additional_equates) = lhs.combine_children(this, &new_children, &new_ty.arity(ctx).into())?;
        required_equates.append(&mut additional_equates);

        let new_upper_bounds = lhs.upper_bounds.union(&rhs.upper_bounds).cloned().collect();
        lhs.commit_update(new_ty, new_children, new_upper_bounds);

        Ok(required_equates)
    }

    fn commit_update(&mut self, new_ty: T, new_children: Children, new_upper_bounds: HashSet<Key>){
        self.ty = new_ty;
        self.children = new_children;
        self.upper_bounds = new_upper_bounds;
    }

    pub(crate) fn with_bound(
        &mut self,
        this: Key,
        bound: T,
        ctx: &T::Context,
    ) -> Result<(), TcErr<T>> {

        let new_ty =
            T::meet(self.ty.clone(), bound.clone(), ctx).map_err(|err| 
                TcErr::IncompatibleBound { key: this, ty: self.ty.clone(), bound, err }
            )?;

        let (new_children, equates) = self.combine_children(this, &self.children, &new_ty.arity(ctx).into())?;
        assert!(equates.is_empty());

        self.children = new_children;
        self.ty = new_ty;

        Ok(())
    }

    pub(crate) fn into_preliminary(self) -> Preliminary<T> {
        Preliminary { ty: self.ty, children: self.children }
    }
}

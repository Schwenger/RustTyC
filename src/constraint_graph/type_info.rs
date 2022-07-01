use std::collections::HashSet;

use crate::{
    subtys::{Equates, ReqsMerge, SubTyAccess, SubTyAccessErr, SubTys},
    type_table::Preliminary,
    ContextType, Key, TcErr,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct TypeInfo<T: ContextType> {
    pub(crate) ty: T,
    pub(crate) subtys: SubTys<T::SubTyId>,
    pub(crate) upper_bounds: HashSet<Key>,
}

impl<T: ContextType> TypeInfo<T> {
    pub(crate) fn top() -> Self {
        TypeInfo { ty: T::top(), subtys: SubTys::top(), upper_bounds: HashSet::new() }
    }

    pub(crate) fn equal(this: &Self, that: &Self, ctx: &T::Context) -> bool {
        T::equal(&this.ty, &that.ty, ctx) && this.subtys == that.subtys && this.upper_bounds == that.upper_bounds
    }

    pub(crate) fn transform_err(key: Key, ty: &T, err: SubTyAccessErr<T::SubTyId>) -> TcErr<T> {
        TcErr::InvalidSubTyAccessInfered(key, ty.clone(), err.subtys, err.accessor)
    }

    pub(crate) fn subty(&self, this: Key, access: SubTyAccess<T::SubTyId>) -> Result<Option<Key>, TcErr<T>> {
        self.subtys.subty(access).map_err(|err| Self::transform_err(this, &self.ty, err))
    }

    pub(crate) fn add_subty(
        &mut self,
        this: Key,
        access: SubTyAccess<T::SubTyId>,
        subty_key: Key,
    ) -> Result<ReqsMerge, TcErr<T>> {
        self.subtys.add_subty(access, subty_key).map_err(|err| Self::transform_err(this, &self.ty, err))
    }

    pub(crate) fn add_upper_bound(&mut self, bound: Key) {
        let _ = self.upper_bounds.insert(bound);
    }

    fn combine_subtys(
        &self,
        this: Key,
        left: &SubTys<T::SubTyId>,
        right: &SubTys<T::SubTyId>,
    ) -> Result<(SubTys<T::SubTyId>, Equates), TcErr<T>> {
        let mut new_subtys = SubTys::empty();

        let all_subtys = left.to_vec().into_iter().chain(right.to_vec().into_iter());
        let required_equates = all_subtys
            .map(|(access, subty_key)| {
                new_subtys.add_potential_subty(*access, *subty_key).map(|merge| merge.zip(*subty_key))
            })
            .collect::<Result<Vec<_>, _>>()
            .map_err(|err| Self::transform_err(this, &self.ty, err))?
            .drain(..)
            .flatten()
            .collect::<Vec<_>>();
        Ok((new_subtys, required_equates))
    }

    pub(crate) fn meet(&mut self, this: Key, that: Key, rhs: &Self, ctx: &T::Context) -> Result<Equates, TcErr<T>> {
        let lhs = self;

        let (new_subtys, mut required_equates) = lhs.combine_subtys(this, &lhs.subtys, &rhs.subtys)?;

        #[cfg(Debug)]
        {
            let new_arity = Self::meet_arity(lhs.ty.arity(ctx), this, rhs.ty.arity(ctx), that)?;
            let debug_subtys = new_subtys.impose(new_arity);
            assert!(debug_subtys.is_ok() && debug_subtys.unwrap() == new_subtys);
        }

        let new_ty = ContextType::meet(lhs.ty.clone(), rhs.ty.clone(), ctx).map_err(|e| TcErr::IncompatibleTypes {
            key1: this,
            ty1: lhs.ty.clone(),
            key2: that,
            ty2: rhs.ty.clone(),
            err: e,
        })?;

        let (new_subtys, mut additional_equates) = lhs.combine_subtys(this, &new_subtys, &new_ty.arity(ctx).into())?;
        required_equates.append(&mut additional_equates);

        let new_upper_bounds = lhs.upper_bounds.union(&rhs.upper_bounds).cloned().collect();
        lhs.commit_update(new_ty, new_subtys, new_upper_bounds);

        Ok(required_equates)
    }

    fn commit_update(&mut self, new_ty: T, new_subtys: SubTys<T::SubTyId>, new_upper_bounds: HashSet<Key>) {
        self.ty = new_ty;
        self.subtys = new_subtys;
        self.upper_bounds = new_upper_bounds;
    }

    pub(crate) fn with_bound(&mut self, this: Key, bound: T, ctx: &T::Context) -> Result<(), TcErr<T>> {
        let new_ty = T::meet(self.ty.clone(), bound.clone(), ctx).map_err(|err| TcErr::IncompatibleBound {
            key: this,
            ty: self.ty.clone(),
            bound,
            err,
        })?;

        let (new_subtys, equates) = self.combine_subtys(this, &self.subtys, &new_ty.arity(ctx).into())?;
        assert!(equates.is_empty());

        self.subtys = new_subtys;
        self.ty = new_ty;

        Ok(())
    }

    pub(crate) fn into_preliminary(self) -> Preliminary<T> {
        Preliminary { ty: self.ty, subtys: self.subtys }
    }
}

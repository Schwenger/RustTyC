use crate::Abstract;
use crate::TcKey;
use crate::{Reifiable, ReificationError, TryReifiable};
use std::collections::HashMap;

pub trait TypeTable {
    type AbsTy: Abstract;
    type Output;

    fn as_hashmap(self) -> HashMap<TcKey<Self::AbsTy>, Self::Output>;
}

#[derive(Debug, Clone)]
pub struct AbstractTypeTable<AbsTy: Abstract> {
    table: HashMap<TcKey<AbsTy>, AbsTy>,
}

impl<AbsTy: Abstract> From<HashMap<TcKey<AbsTy>, AbsTy>> for AbstractTypeTable<AbsTy> {
    fn from(map: HashMap<TcKey<AbsTy>, AbsTy>) -> Self {
        AbstractTypeTable { table: map }
    }
}

#[derive(Debug, Clone)]
pub struct ReifiedTypeTable<AbsTy: Abstract, Concrete> {
    table: HashMap<TcKey<AbsTy>, Concrete>,
}

impl<AbsTy: Abstract, Concrete> From<HashMap<TcKey<AbsTy>, Concrete>> for ReifiedTypeTable<AbsTy, Concrete> {
    fn from(map: HashMap<TcKey<AbsTy>, Concrete>) -> Self {
        ReifiedTypeTable { table: map }
    }
}

impl<AbsTy: Abstract> TypeTable for AbstractTypeTable<AbsTy> {
    type AbsTy = AbsTy;
    type Output = AbsTy;

    fn as_hashmap(self) -> HashMap<TcKey<Self::AbsTy>, Self::Output> {
        self.table
    }
}

impl<AbsTy> TypeTable for ReifiedTypeTable<AbsTy, AbsTy::Reified>
where
    AbsTy: Abstract + Reifiable,
{
    type AbsTy = AbsTy;
    type Output = AbsTy::Reified;

    fn as_hashmap(self) -> HashMap<TcKey<Self::AbsTy>, Self::Output> {
        self.table
    }
}

impl<AbsTy> AbstractTypeTable<AbsTy>
where
    AbsTy: Abstract + Reifiable,
{
    pub fn reified(self) -> ReifiedTypeTable<AbsTy, AbsTy::Reified> {
        ReifiedTypeTable { table: self.table.into_iter().map(|(key, ty)| (key, ty.reify())).collect() }
    }
}

impl<AbsTy> AbstractTypeTable<AbsTy>
where
    AbsTy: Abstract + TryReifiable,
{
    pub fn try_reified(self) -> Result<ReifiedTypeTable<AbsTy, AbsTy::Reified>, ()> {
        self.table
            .into_iter()
            .map(|(key, ty)| ty.try_reify().map(|re| (key, re)))
            .collect::<Result<HashMap<TcKey<AbsTy>, AbsTy::Reified>, ReificationError>>()
            .map_err(|_| ())
            .map(|table| ReifiedTypeTable { table })
    }
}

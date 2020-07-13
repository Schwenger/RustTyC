use crate::Abstract;
use crate::TcKey;
use crate::{Reifiable, ReificationError, TryReifiable};
use std::collections::HashMap;

pub trait TypeTable {
    type Type;

    fn as_hashmap(self) -> HashMap<TcKey, Self::Type>;
}

#[derive(Debug, Clone)]
pub struct AbstractTypeTable<AbsTy: Abstract> {
    table: HashMap<TcKey, AbsTy>,
}

impl<AbsTy: Abstract> From<HashMap<TcKey, AbsTy>> for AbstractTypeTable<AbsTy> {
    fn from(map: HashMap<TcKey, AbsTy>) -> Self {
        AbstractTypeTable { table: map }
    }
}

#[derive(Debug, Clone)]
pub struct ReifiedTypeTable<Concrete> {
    table: HashMap<TcKey, Concrete>,
}

impl<Concrete> From<HashMap<TcKey, Concrete>> for ReifiedTypeTable<Concrete> {
    fn from(map: HashMap<TcKey, Concrete>) -> Self {
        ReifiedTypeTable { table: map }
    }
}

impl<AbsTy: Abstract> TypeTable for AbstractTypeTable<AbsTy> {
    type Type = AbsTy;

    fn as_hashmap(self) -> HashMap<TcKey, Self::Type> {
        self.table
    }
}

impl<Concrete> TypeTable for ReifiedTypeTable<Concrete> {
    type Type = Concrete;

    fn as_hashmap(self) -> HashMap<TcKey, Self::Type> {
        self.table
    }
}

impl<AbsTy> AbstractTypeTable<AbsTy>
where
    AbsTy: Abstract + Reifiable,
{
    pub fn reified(self) -> ReifiedTypeTable<AbsTy::Reified> {
        ReifiedTypeTable { table: self.table.into_iter().map(|(key, ty)| (key, ty.reify())).collect() }
    }
}

impl<AbsTy> AbstractTypeTable<AbsTy>
where
    AbsTy: Abstract + TryReifiable,
{
    pub fn try_reified(self) -> Result<ReifiedTypeTable<AbsTy::Reified>, ()> {
        self.table
            .into_iter()
            .map(|(key, ty)| ty.try_reify().map(|re| (key, re)))
            .collect::<Result<HashMap<TcKey, AbsTy::Reified>, ReificationError>>()
            .map_err(|_| ())
            .map(|table| ReifiedTypeTable { table })
    }
}

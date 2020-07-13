use std::hash::Hash;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TcKey {
    pub(crate) ix: usize,
}

impl TcKey {
    pub(crate) fn new(ix: usize) -> TcKey {
        TcKey { ix }
    }
}

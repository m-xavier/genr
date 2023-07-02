#![allow(unused)]

use std::{
    ops::{Index, IndexMut},
    vec::IntoIter as VecIntoIter,
};

use crate::gen::*;

#[macro_export]
macro_rules! gvec {
    () => {
        GVec::new()
    };
    ($($item:tt),*) => {
        GVec::from([$($item),*])
    };
}
pub(crate) use gvec;

/// A generational container which is dynamically sized, similar to a `Vec`.
/// 
/// `GVec` promises to uphold the following rules:
///
/// 1. Inserting an item returns a `GIdx`, which must be valid for
/// as long as that item exists.
///
/// 2. Removing an item invalidates the associated `GIdx`, freeing up
/// its spot to be used by new data.
///
/// 3. If another item is inserted afterwards, the ABA problem is
/// prevented via the use of "generations".
///
/// Note that `GVec` does not promise that a `GIdx` provided by you was sourced 
/// from the same `GVec`. Using a `GIdx` from a different `GVec` will result in 
/// the retrieval of an unexpected value.
#[derive(Clone)]
pub struct GVec<T> {
    data: Vec<Option<T>>,
    gens: Vec<usize>,
    dead: Vec<usize>,
}

impl<T> GVec<T> {
    /// Returns a new, empty `GVec`.
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            gens: Vec::new(),
            dead: Vec::new(),
        }
    }
    /// Returns a tuple containing a new `GVec` filled with the contents of
    /// `value` and an array containing their corresponding indices.
    pub fn from<const N: usize>(value: [T; N]) -> (Self, [GIdx; N]) {
        let mut i = 0;
        (
            Self {
                data: Vec::from(value.map(|v| Some(v))),
                gens: Vec::from([0; N]),
                dead: Vec::new(),
            },
            [GIdx { idx: 0, gen: 0 }; N].map(|mut g| {
                g.idx = i;
                i += 1;
                g
            }),
        )
    }
}

impl<T> Index<GIdx> for GVec<T> {
    type Output = T;
    fn index(&self, gidx: GIdx) -> &Self::Output {
        assert!(self.contains(gidx));
        self.data[gidx.idx].as_ref().unwrap()
    }
}

impl<T> IndexMut<GIdx> for GVec<T> {
    fn index_mut(&mut self, gidx: GIdx) -> &mut Self::Output {
        assert!(self.contains(gidx));
        self.data[gidx.idx].as_mut().unwrap()
    }
}

impl<T> IntoIterator for GVec<T> {
    type Item = T;
    type IntoIter = IntoIter<T, VecIntoIter<Option<T>>>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.data.into_iter(),
        }
    }
}

impl<T> Gen<T> for GVec<T> {
    type IntoIterKind = VecIntoIter<Option<T>>;

    fn count(&self) -> usize {
        self.data.iter().fold(0, |acc, i| acc + i.is_some() as usize)
    }

    fn contains(&self, gidx: GIdx) -> bool {
        gidx.idx < self.gens.len()
            && gidx.gen == self.gens[gidx.idx]
            && self.data[gidx.idx].is_some()
    }

    fn insert(&mut self, item: T) -> GIdx {
        match self.dead.pop() {
            Some(idx) => {
                self.data[idx] = Some(item);
                self.gens[idx] += 1;
                GIdx { idx, gen: self.gens[idx] }
            },
            None => {
                self.data.push(Some(item));
                self.gens.push(0);
                GIdx { idx: self.data.len() - 1, gen: 0 }
            }
        }
    }
    fn remove(&mut self, gidx: GIdx) -> Option<T> {
        self.contains(gidx).then(|| {
            self.gens[gidx.idx] += 1;
            self.dead.push(gidx.idx);
            self.data[gidx.idx].take().unwrap()
        })
    }

    fn clear(&mut self) {
        self.dead = (0..self.data.len()).collect();
        for item in self.data.iter_mut() { *item = None }
    }
    fn extract(&mut self) -> Vec<T> {
        self.dead = (0..self.data.len()).collect();
        self.data.iter_mut().filter_map(|i| i.take()).collect()
    }

    fn get(&self, gidx: GIdx) -> Option<&T> {
        self.contains(gidx).then(|| self.data[gidx.idx].as_ref().unwrap())
    }
    fn get_mut(&mut self, gidx: GIdx) -> Option<&mut T> {
        self.contains(gidx).then(|| self.data[gidx.idx].as_mut().unwrap())
    }

    fn set(&mut self, gidx: GIdx, value: T) -> Option<T> {
        self.contains(gidx).then(|| self.data[gidx.idx].replace(value).unwrap())
    }

    fn iter(&self) -> Iter<'_, T> {
        Iter::<'_, T> {
            inner: self.data.iter(),
        }
    }
    fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut::<'_, T> {
            inner: self.data.iter_mut(),
        }
    }

    fn gather(&self) -> Vec<&T> {
        self.data.iter().filter_map(|i| i.as_ref()).collect()
    }
    fn gather_mut(&mut self) -> Vec<&mut T> {
        self.data.iter_mut().filter_map(|i| i.as_mut()).collect()
    }
}

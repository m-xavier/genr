#![allow(unused)]

use std::{
    ops::{Index, IndexMut},
    vec::IntoIter as VecIntoIter,
};

use crate::generational::*;

#[macro_export]
macro_rules! gvec {
    () => {
        GVec::new()
    };
    ($($item:tt),*) => {
        GVec::from([$($item),*])
    };
}
pub use gvec;

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
#[derive(Clone, Debug, Default)]
pub struct GVec<T> {
    data: Vec<Option<T>>,
    gens: Vec<usize>,
    dead: Vec<usize>,
}

impl<T> GVec<T> {
    /// Returns a new, empty `GVec`.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let chars: GVec<char> = GVec::new();
    /// assert!(chars.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            gens: Vec::new(),
            dead: Vec::new(),
        }
    }

    /// Returns a tuple containing a new `GVec` filled with the contents of
    /// `value` and an array containing their corresponding indices.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (chars, [a, b, c]) = GVec::from(['a', 'b', 'c']);
    /// assert_eq!(chars[a], 'a');
    /// assert_eq!(chars[b], 'b');
    /// assert_eq!(chars[c], 'c');
    /// ```
    pub fn from<const N: usize>(value: [T; N]) -> (Self, [GIdx; N]) {
        let mut idxs = 0..N;
        (
            Self {
                data: Vec::from(value.map(|v| Some(v))),
                gens: Vec::from([0; N]),
                dead: Vec::new(),
            },
            [GIdx { idx: 0, gen: 0 }; N].map(|mut g| {
                g.idx = idxs.next().unwrap(); g
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

impl<T> Generational<T> for GVec<T> {
    type OwnedIter = VecIntoIter<Option<T>>;

    /// Returns the number of valid elements in `self`.
    /// This may not be representative of the actual underlying length.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = gvec!['a', 'b', 'c'];
    /// assert_eq!(chars.count(), 3);
    ///
    /// chars.remove(b);
    /// assert_eq!(chars.count(), 2);
    /// ```
    fn count(&self) -> usize {
        self.data
            .iter()
            .fold(0, |acc, i| acc + i.is_some() as usize)
    }

    /// Returns `true` if there are no valid elements in `self`, otherwise
    /// returns `false`.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, _) = gvec!['a', 'b', 'c'];
    /// chars.clear();
    ///
    /// assert!(chars.is_empty());
    /// ```
    fn is_empty(&self) -> bool {
        self.dead.len() == self.data.len()
    }

    /// Returns `true` if the index passed refers to a valid element.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = gvec!['a', 'b', 'c'];
    /// assert_eq!(chars.contains(b), true);
    ///
    /// chars.remove(b);
    /// assert_eq!(chars.contains(b), false);
    /// ```
    fn contains(&self, gidx: GIdx) -> bool {
        gidx.idx < self.gens.len()
            && gidx.gen == self.gens[gidx.idx]
            && self.data[gidx.idx].is_some()
    }

    /// Inserts an item into `self`, returning an index which refers to it.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let mut chars = gvec![];
    /// let a = chars.insert('a');
    ///
    /// assert_eq!(chars[a], 'a');
    /// ```
    fn insert(&mut self, item: T) -> GIdx {
        match self.dead.pop() {
            Some(idx) => {
                self.data[idx] = Some(item);
                self.gens[idx] += 1;
                GIdx {
                    idx,
                    gen: self.gens[idx],
                }
            }
            None => {
                self.data.push(Some(item));
                self.gens.push(0);
                GIdx {
                    idx: self.data.len() - 1,
                    gen: 0,
                }
            }
        }
    }

    /// Removes the item from `self`, returning `Some(T)` if the
    /// index is valid, or `None` if the index is not.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = gvec!['a', 'b', 'c'];
    /// assert_eq!(chars.remove(a), Some('a'));
    /// assert_eq!(chars.remove(b), Some('b'));
    /// assert_eq!(chars.remove(c), Some('c'));
    /// assert_eq!(chars.count(), 0);
    /// ```
    fn remove(&mut self, gidx: GIdx) -> Option<T> {
        self.contains(gidx).then(|| {
            self.gens[gidx.idx] += 1;
            self.dead.push(gidx.idx);
            self.data[gidx.idx].take().unwrap()
        })
    }

    /// Clears `self`, removing all values.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, _) = gvec!['a', 'b', 'c'];
    /// chars.clear();
    ///
    /// assert_eq!(chars.count(), 0);
    /// ```
    fn clear(&mut self) {
        self.dead = (0..self.data.len()).collect();
        for item in self.data.iter_mut() {
            *item = None
        }
    }

    /// Clears `self`, returning any valid data in a `Vec`.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, _) = gvec!['a', 'b', 'c'];
    /// let vec_chars = chars.extract();
    ///
    /// assert_eq!(chars.count(), 0);
    /// assert_eq!(vec_chars, vec!['a', 'b', 'c']);
    /// ```
    fn extract(&mut self) -> Vec<T> {
        self.dead = (0..self.data.len()).collect();
        self.data.iter_mut().filter_map(|i| i.take()).collect()
    }

    /// Returns `Some(&T)` if the index is valid or `None` if the
    /// index is not.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (chars, [a, b, c]) = gvec!['a', 'b', 'c'];
    /// assert_eq!(chars.get(b), Some(&'b'));
    /// ```
    fn get(&self, gidx: GIdx) -> Option<&T> {
        self.contains(gidx)
            .then(|| self.data[gidx.idx].as_ref().unwrap())
    }

    /// Returns `Some(&mut T)` if the index is valid or `None` if the
    /// index is not.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = gvec!['a', 'b', 'c'];
    /// assert_eq!(chars.get_mut(b), Some(&mut 'b'));
    /// ```
    fn get_mut(&mut self, gidx: GIdx) -> Option<&mut T> {
        self.contains(gidx)
            .then(|| self.data[gidx.idx].as_mut().unwrap())
    }

    /// Sets the value at the provided index to `value`, returning
    /// either the original value or `None` if the index is invalid.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = gvec!['a', 'b', 'c'];
    /// let original = chars.set(b, 'B');
    ///
    /// assert_eq!(chars[b], 'B');
    /// assert_eq!(original, Some('b'));
    /// ```
    fn set(&mut self, gidx: GIdx, value: T) -> Option<T> {
        self.contains(gidx)
            .then(|| self.data[gidx.idx].replace(value).unwrap())
    }

    /// Returns an iterator which iterates over all values.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (chars, _) = gvec!['a', 'b', 'c'];
    /// let mut iterator = chars.iter();
    ///
    /// assert_eq!(iterator.next(), Some(&'a'));
    /// assert_eq!(iterator.next(), Some(&'b'));
    /// assert_eq!(iterator.next(), Some(&'c'));
    /// assert_eq!(iterator.next(), None);
    /// ```
    fn iter(&self) -> Iter<'_, T> {
        Iter::<'_, T> {
            inner: self.data.iter(),
        }
    }

    /// Returns an iterator which mutably iterates over all values.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, _) = gvec!['a', 'b', 'c'];
    /// let mut iterator = chars.iter_mut();
    ///
    /// assert_eq!(iterator.next(), Some(&mut 'a'));
    /// assert_eq!(iterator.next(), Some(&mut 'b'));
    /// assert_eq!(iterator.next(), Some(&mut 'c'));
    /// assert_eq!(iterator.next(), None);
    /// ```
    fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut::<'_, T> {
            inner: self.data.iter_mut(),
        }
    }

    /// Returns a `Vec` containing a reference to all values.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (chars, _) = gvec!['a', 'b', 'c'];
    /// assert_eq!(chars.gather(), vec![&'a', &'b', &'c']);
    /// ```
    fn gather(&self) -> Vec<&T> {
        self.data.iter().filter_map(|i| i.as_ref()).collect()
    }

    /// Returns a `Vec` containing a mutable reference to all values.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, _) = gvec!['a', 'b', 'c'];
    /// assert_eq!(chars.gather_mut(), vec![&mut 'a', &mut 'b', &mut 'c']);
    /// ```
    fn gather_mut(&mut self) -> Vec<&mut T> {
        self.data.iter_mut().filter_map(|i| i.as_mut()).collect()
    }
}

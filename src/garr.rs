#![allow(unused)]

use std::{
    ops::{Index, IndexMut},
    array::IntoIter as ArrIntoIter,
};

use crate::generational::*;

/// A convenience macro for creating `GArr`s.
/// 
/// # Examples
/// ```
/// # use genr::prelude::*;
/// let empty_a = garr![;char, 3];
/// let empty_b: GArr<char, 3> = GArr::new();
/// assert_eq!(empty_a.gather(), empty_b.gather());
/// 
/// let (from_a, _) = garr!['a', 'b', 'c'];
/// let (from_b, _) = GArr::from(['a', 'b', 'c']);
/// assert_eq!(from_a.gather(), from_b.gather());
///
/// let (partial_a, _) = garr!['a', 'b', 'c'; char, 5];
/// let (partial_b, _) = GArr::<char, 5>::from_partial(['a', 'b', 'c']);
/// assert_eq!(partial_a.gather(), partial_b.gather())
/// ```
#[macro_export]
macro_rules! garr {
    () => {
        GArr::new()
    };
    (;$t:ty,$n:tt) => {
        GArr::<$t, $n>::new()
    };
    ($($item:tt),*) => {
        GArr::from([$($item),*])
    };
    ($item:tt;$n:tt) => {
        GArr::from([$item; $n])
    };
    ($($item:tt),+;$t:ty,$n:tt) => {
        GArr::<$t, $n>::from_partial([$($item),*])
    };
}
pub use garr;

/// A generational container which is statically sized, just like a primitive array.
///
/// `GArr` promises to uphold the following rules:
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
/// Note that `GArr` does not promise that a `GIdx` provided by you was sourced
/// from the same `GArr`. Using a `GIdx` from a different `GArr` will result in
/// the retrieval of an unexpected value.
/// 
/// As `GArr` is also statically sized, there is a chance that inserting may fail 
/// if it is at capacity, panicking. 
#[derive(Clone, Debug)]
pub struct GArr<T, const N: usize> {
    data: [Option<T>; N],
    gens: [usize; N],
    dead: Vec<usize>,
    used: usize,
}

impl<T, const N: usize> GArr<T, N> {
    /// Returns a new, empty `GArr`.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let chars: GArr<char, 3> = GArr::new();
    /// assert!(chars.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            data: std::array::from_fn(|_| None),
            gens: [0; N],
            dead: Vec::with_capacity(N),
            used: 0,
        }
    }

    /// Returns a tuple containing a new `GArr` filled with the contents of
    /// `value` and an array containing their corresponding indices.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (chars, [a, b, c]): (GArr<char, 3>, [GIdx; 3]) = GArr::from(['a', 'b', 'c']);
    /// assert_eq!(chars[a], 'a');
    /// assert_eq!(chars[b], 'b');
    /// assert_eq!(chars[c], 'c');
    /// ```
    pub fn from(value: [T; N]) -> (Self, [GIdx; N]) {
        (
            Self {
                data: value.map(|i| Some(i)),
                gens: [0; N],
                dead: Vec::with_capacity(N),
                used: N,
            },
            std::array::from_fn(|i| GIdx { idx: i, gen: 0 }),
        )
    }

    /// Returns a tuple containing a new `GArr` filled with the contents of
    /// `value` and an array containing their corresponding indices.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (chars, [a, b, c]) = GArr::<char, 5>::from_partial(['a', 'b', 'c']);
    /// assert_eq!(chars[a], 'a');
    /// assert_eq!(chars[b], 'b');
    /// assert_eq!(chars[c], 'c');
    /// ```
    pub fn from_partial<const TN: usize>(value: [T; TN]) -> (Self, [GIdx; TN]) {
        let mut out = Self::new();
        let out_idxs = out.insert_arr(value).map(|idx| idx.unwrap());
        (out, out_idxs)
    }

    /// Returns `true` if all indexes are occupied, otherwise returns `false`.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let mut chars: GArr<char, 3> = garr![];
    /// assert!(chars.is_empty());
    ///
    /// chars.insert_arr(['a', 'b', 'c']);
    /// assert!(chars.is_full())
    /// ```
    pub fn is_full(&self) -> bool {
        println!("{}, {}, {}", self.used, N, self.count());
        self.used == N && self.dead.is_empty()
    }
}

impl<T, const N: usize> Default for GArr<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, const N: usize> Index<GIdx> for GArr<T, N> {
    type Output = T;
    fn index(&self, gidx: GIdx) -> &Self::Output {
        assert!(self.contains(gidx));
        self.data[gidx.idx].as_ref().unwrap()
    }
}

impl<T, const N: usize> IndexMut<GIdx> for GArr<T, N> {
    fn index_mut(&mut self, gidx: GIdx) -> &mut Self::Output {
        assert!(self.contains(gidx));
        self.data[gidx.idx].as_mut().unwrap()
    }
}

impl<T, const N: usize> IntoIterator for GArr<T, N> {
    type Item = T;
    type IntoIter = IntoIter<T, ArrIntoIter<Option<T>, N>>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.data.into_iter(),
        }
    }
}

impl<T, const N: usize> Generational<T> for GArr<T, N> {
    type OwnedIter = ArrIntoIter<Option<T>, N>;
    type InsertResult = Result<GIdx, &'static str>;

    /// Returns the number of valid elements in `self`.
    /// This may not be representative of the actual underlying length.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = garr!['a', 'b', 'c'];
    /// assert_eq!(chars.count(), 3);
    ///
    /// chars.remove(b);
    /// assert_eq!(chars.count(), 2);
    /// ```
    fn count(&self) -> usize {
        self.used - self.dead.len()
    }

    /// Returns `true` if there are no valid elements in `self`, otherwise
    /// returns `false`.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, _) = garr!['a', 'b', 'c'];
    /// assert!(!chars.is_empty());
    ///
    /// chars.clear();
    /// assert!(chars.is_empty());
    /// ```
    fn is_empty(&self) -> bool {
        self.dead.len() == self.used
    }

    /// Returns `true` if the index passed refers to a valid element.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = garr!['a', 'b', 'c'];
    /// assert_eq!(chars.contains(b), true);
    ///
    /// chars.remove(b);
    /// assert_eq!(chars.contains(b), false);
    /// ```
    fn contains(&self, gidx: GIdx) -> bool {
        gidx.idx < self.used
            && gidx.gen == self.gens[gidx.idx]
            && self.data[gidx.idx].is_some()
    }

    /// Inserts an item into `self`, returning a `Result<GIdx>`.
    /// If there is no more space available, this will return `Err`.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let mut chars: GArr<char, 5> = garr![];
    /// let a = chars.insert('a').unwrap();
    ///
    /// assert_eq!(chars[a], 'a');
    /// ```
    fn insert(&mut self, item: T) -> Self::InsertResult {
        if self.is_full() { return Err("insert failed, GArr is at capacity") }
        Ok(match self.dead.pop() {
            Some(idx) => {
                self.data[idx] = Some(item);
                self.gens[idx] += 1;
                GIdx {
                    idx,
                    gen: self.gens[idx],
                }
            }
            None => {
                self.data[self.used] = Some(item);
                self.gens[self.used] += 1;
                self.used += 1;
                GIdx {
                    idx: self.used - 1,
                    gen: 1,
                }
            }
        })
    }

    /// Removes the item from `self`, returning `Some(T)` if the
    /// index is valid, or `None` if the index is not.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = garr!['a', 'b', 'c'];
    /// assert_eq!(chars.remove(a), Some('a'));
    /// assert_eq!(chars.remove(b), Some('b'));
    /// assert_eq!(chars.remove(c), Some('c'));
    /// assert_eq!(chars.count(), 0);
    /// ```
    fn remove(&mut self, gidx: GIdx) -> Option<T> {
        self.contains(gidx).then(|| {
            self.dead.push(gidx.idx);
            self.data[gidx.idx].take().unwrap()
        })
    }

    /// Clears `self`, removing all values.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, _) = garr!['a', 'b', 'c'];
    /// chars.clear();
    ///
    /// assert_eq!(chars.count(), 0);
    /// ```
    fn clear(&mut self) {
        self.dead = (0..N).collect();
        self.data.iter_mut().for_each(|item| {*item = None})
    }

    /// Clears `self`, returning any valid data in a `Vec`.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, _) = garr!['a', 'b', 'c'];
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
    /// let (chars, [a, b, c]) = garr!['a', 'b', 'c'];
    /// assert_eq!(chars.get(b), Some(&'b'));
    /// ```
    fn get(&self, gidx: GIdx) -> Option<&T> {
        self.contains(gidx).then(|| self.data[gidx.idx].as_ref().unwrap())
    }

    /// Returns `Some(&mut T)` if the index is valid or `None` if the
    /// index is not.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = garr!['a', 'b', 'c'];
    /// assert_eq!(chars.get_mut(b), Some(&mut 'b'));
    /// ```
    fn get_mut(&mut self, gidx: GIdx) -> Option<&mut T> {
        self.contains(gidx).then(|| self.data[gidx.idx].as_mut().unwrap())
    }

    /// Sets the value at the provided index to `value`, returning
    /// either the original value or `None` if the index is invalid.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (mut chars, [a, b, c]) = garr!['a', 'b', 'c'];
    /// let original = chars.set(b, 'B');
    ///
    /// assert_eq!(chars[b], 'B');
    /// assert_eq!(original, Some('b'));
    /// ```
    fn set(&mut self, gidx: GIdx, value: T) -> Option<T> {
        self.contains(gidx).then(|| self.data[gidx.idx].replace(value).unwrap())
    }

    /// Returns an iterator which iterates over all values.
    ///
    /// # Examples
    /// ```
    /// # use genr::prelude::*;
    /// let (chars, _) = garr!['a', 'b', 'c'];
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
    /// let (mut chars, _) = garr!['a', 'b', 'c'];
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
    /// let (chars, _) = garr!['a', 'b', 'c'];
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
    /// let (mut chars, _) = garr!['a', 'b', 'c'];
    /// assert_eq!(chars.gather_mut(), vec![&mut 'a', &mut 'b', &mut 'c']);
    /// ```
    fn gather_mut(&mut self) -> Vec<&mut T> {
        self.data.iter_mut().filter_map(|i| i.as_mut()).collect()
    }
}

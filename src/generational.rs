#![allow(unused)]

use std::ops::{Index, IndexMut};

/// Short for "Generational Index". A `GIdx` can only be created by a
/// structure which implements `Generational`, and will only refer to
/// the intended value if used with the original source struct.
#[derive(Clone, Copy, Debug)]
pub struct GIdx {
    pub(crate) idx: usize,
    pub(crate) gen: usize,
}

/// An iterator over all valid data in a `Generational` container.
#[derive(Clone, Debug)]
pub struct Iter<'a, T> {
    pub(crate) inner: std::slice::Iter<'a, Option<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.find(|t| t.is_some())?.as_ref()
    }
}

/// A mutable iterator over all valid data in a `Generational` container.
#[derive(Debug)]
pub struct IterMut<'a, T> {
    pub(crate) inner: std::slice::IterMut<'a, Option<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.find(|t| t.is_some())?.as_mut()
    }
}

/// An owned iterator over all valid data in a `Generational` container.
#[derive(Debug)]
pub struct IntoIter<T, I>
where
    I: Iterator<Item = Option<T>>,
{
    pub(crate) inner: I,
}

impl<T, I> Iterator for IntoIter<T, I>
where
    I: Iterator<Item = Option<T>>,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.find(|t| t.is_some())?
    }
}

/// Describes a data structure which supports generational indexing.
/// Any implementer of `Generational` must uphold the following rules:
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
/// Note that a `Generational` data structure does not promise that a `GIdx` provided
/// by you was sourced from the same struct. Using a `GIdx` from a different
/// struct will result in the retrieval of an unexpected value.
pub trait Generational<T>
where
    Self: IntoIterator<Item = T, IntoIter = IntoIter<T, Self::OwnedIter>>
        + Index<GIdx>
        + IndexMut<GIdx>,
    Self::OwnedIter: Iterator<Item = Option<T>>,
{
    type OwnedIter;
    type InsertResult;
    
    /// Returns the number of valid elements in `self`.
    /// This may not be representative of the actual underlying length.
    fn count(&self) -> usize;
    /// Returns `true` if there are no valid elements in `self`, otherwise
    /// returns `false`.
    fn is_empty(&self) -> bool;

    /// Returns `true` if the index passed refers to a valid element.
    fn contains(&self, gidx: GIdx) -> bool;

    /// Inserts an item into `self`, returning an index which refers to it.
    fn insert(&mut self, item: T) -> Self::InsertResult;
    /// Inserts an array of multiple items into `self`, returning the corresponding `GIdx`s
    /// in an array.
    fn insert_arr<const N: usize>(&mut self, items: [T; N]) -> [Self::InsertResult; N] {
        items.into_iter().zip(0..N).fold(
            std::array::from_fn(|_| None),
            |mut acc, (item, idx)| {
                acc[idx] = Some(self.insert(item)); acc
            }
        ).map(|gidx| gidx.unwrap())
    }
    /// Inserts a slice of multiple items into `self`, returning the corresponding `GIdx`s
    /// in a vec.
    fn insert_slice(&mut self, items: &[T]) -> Vec<Self::InsertResult>
        where T: Clone
    {
        items.into_iter().fold(
            vec![],
            |mut acc, item| {
                acc.push(self.insert(item.clone())); acc
            }
        )
    }
    /// Inserts a slice of multiple items into `self`, returning the corresponding `GIdx`s
    /// in a vec.
    fn insert_vec(&mut self, items: Vec<T>) -> Vec<Self::InsertResult> {
        items.into_iter().fold(
            vec![],
            |mut acc, item| {
                acc.push(self.insert(item)); acc
            }
        )
    }
    /// Removes the item from `self`, returning `Some(T)` if the
    /// index is valid, or `None` if the index is not.
    fn remove(&mut self, gidx: GIdx) -> Option<T>;

    /// Clears `self`, removing all values.
    fn clear(&mut self);
    /// Clears `self`, returning any valid data in a `Vec`.
    fn extract(&mut self) -> Vec<T>;

    /// Returns `Some(&T)` if the index is valid or `None` if the
    /// index is not.
    fn get(&self, gidx: GIdx) -> Option<&T>;
    /// Returns `Some(&mut T)` if the index is valid or `None` if the
    /// index is not.
    fn get_mut(&mut self, gidx: GIdx) -> Option<&mut T>;
    /// Sets the value at the provided index to `value`, returning
    /// either the original value or `None` if the index is invalid.
    fn set(&mut self, gidx: GIdx, value: T) -> Option<T>;

    /// Returns an iterator which iterates over all values.
    fn iter(&self) -> Iter<'_, T>;
    /// Returns an iterator which mutably iterates over all values.
    fn iter_mut(&mut self) -> IterMut<'_, T>;

    /// Returns a `Vec` containing a reference to all values.
    fn gather(&self) -> Vec<&T>;
    /// Returns a `Vec` containing a mutable reference to all values.
    fn gather_mut(&mut self) -> Vec<&mut T>;
}

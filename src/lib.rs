//! A fixed-size free-list with optional key lifetime safety and macroless unique typing.
#![doc(html_root_url = "https://docs.rs/fixed_free_list")]
#![crate_name = "fixed_free_list"]
#![warn(
    missing_debug_implementations,
    trivial_casts,
    trivial_numeric_casts,
    unused_lifetimes,
    unused_import_braces,
    clippy::shadow_unrelated
)]
#![deny(missing_docs, unaligned_references, unsafe_op_in_unsafe_fn)]
#![cfg_attr(all(nightly, feature = "unstable"), feature(maybe_uninit_uninit_array))]

use std::{
    fmt::{Debug, Formatter, Result},
    marker::PhantomData,
    mem::{self, ManuallyDrop, MaybeUninit},
};

union Block<T> {
    value: ManuallyDrop<T>,
    next: usize,
}

/// A fixed-size free-list.
///
/// # Time Complexity
///
/// All operations are worst case O(1) unless noted otherwise
///
/// # Examples
///
/// ```
/// # use fixed_free_list::*;
/// let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
/// let key1 = list.alloc(8).unwrap();
/// let key2 = list.alloc(5).unwrap();
/// assert_eq!(unsafe { *list.get_unchecked(key1) }, 8);
/// assert_eq!(unsafe { *list.get_unchecked(key2) }, 5);
/// let value = unsafe { list.get_mut_unchecked(key1) };
/// *value = 2;
/// assert_eq!(unsafe { list.free_unchecked(key1) }, 2);
/// assert!(list.is_free(key1));
/// assert_eq!(list.size_hint(), 2);
/// let key3 = list.alloc(7).unwrap();
/// assert_eq!(list.size_hint(), 2);
/// list.clear();
/// assert!(list.is_free(key3));
/// ```
pub struct FixedFreeList<T, const N: usize> {
    next: usize,
    high: usize,
    data: [MaybeUninit<Block<T>>; N],
}

impl<T, const N: usize> FixedFreeList<T, N> {
    /// Creates a new empty `FixedFreeList`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
    /// ```
    #[inline(always)]
    pub fn new() -> Self {
        Self {
            next: N,
            high: 0,
            #[cfg(all(nightly, feature = "unstable"))]
            data: MaybeUninit::uninit_array(),
            #[cfg(not(all(nightly, feature = "unstable")))]
            data: unsafe { MaybeUninit::uninit().assume_init() },
        }
    }

    /// If there is space, adds `value` to the free list and returns its key.
    /// If there is no space, Drops `value` and returns `None`.
    ///
    /// # Returns
    ///
    /// `None` if the list was already full.
    /// Note: `value` is dropped in this case. Check [`is_full`] beforehand to avoid this if desired.
    ///
    /// `Some(key)` if there was spare capacity to accommodate `value`.
    /// `key` can now be used to access `value` via [`get_unchecked`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
    /// list.alloc(1);
    /// ```
    pub fn alloc(&mut self, value: T) -> Option<usize> {
        let key;
        if self.next < N {
            // Use a previously used but now free space
            key = self.next;
            // Update `next` to point at the next free space now that the current one will be used
            // # Safety
            // This space is guaranteed to be free, because otherwise `next` wouldn't point at it.
            self.next = unsafe { self.data.get_unchecked(key).assume_init_ref().next };
        } else {
            if self.high >= N {
                // Drops `value`
                return None;
            }
            // Use a fresh uninitialized space
            key = self.high;
            // Bump high-water mark
            self.high += 1;
        };
        // Dropping is unneccessary here because `data[key]` is either `usize` or `MaybeUninit<T>::uninit()`
        unsafe {
            *self.data.get_unchecked_mut(key) = MaybeUninit::new(Block {
                value: ManuallyDrop::new(value),
            });
        }
        Some(key)
    }

    /// Solely intended for verification purposes.
    /// If your algorithm needs this you're probably doing something wrong.
    ///
    /// # Time Complexity
    ///
    /// Worst case O(N)
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
    /// assert_eq!(list.is_free(0), true);
    /// let key = list.alloc(1).unwrap();
    /// assert_eq!(list.is_free(0), false);
    /// unsafe { list.free_unchecked(key); }
    /// assert_eq!(list.is_free(0), true);
    /// ```
    pub fn is_free(&self, key: usize) -> bool {
        if key >= self.high {
            return true;
        }
        let mut next = self.next;
        while next < N {
            if next == key {
                return true;
            }
            next = unsafe { self.data.get_unchecked(next).assume_init_ref().next };
        }
        false
    }

    /// Frees the space occupied by the value at `key` and returns the value.
    ///
    /// # Returns
    ///
    /// The value at `key`.
    ///
    /// # Safety
    ///
    /// `key` must have originated from calling [`alloc`] on the same instance
    /// and the space must not already been freed since the [`alloc`] call.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
    /// let key = list.alloc(1).unwrap();
    /// let value = unsafe { list.free_unchecked(key) };
    /// assert_eq!(value, 1);
    /// ```
    #[inline(always)]
    pub unsafe fn free_unchecked(&mut self, key: usize) -> T {
        #[cfg(all(feature = "strict"))]
        assert!(!self.is_free(key));

        let value = mem::replace(
            unsafe { self.data.get_unchecked_mut(key) },
            MaybeUninit::new(Block { next: self.next }),
        );

        self.next = key;

        // # Safety
        // Function invariants imply the space is occupied by an initialized value
        ManuallyDrop::into_inner(unsafe { value.assume_init().value })
    }

    /// Provides immutable access to the value at `key`.
    ///
    /// # Returns
    ///
    /// An immutable borrow of the value at `key`.
    ///
    /// # Safety
    ///
    /// `key` must have originated from calling [`alloc`] on the same instance
    /// and the space must not already been freed since the [`alloc`] call.
    ///
    /// There must be no existing mutable borrow of the value at `key` via [`get_mut_unchecked`].
    /// Multiple immutable borrows are permitted.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
    /// let key = list.alloc(1).unwrap();
    /// let value = unsafe { list.get_unchecked(key) };
    /// assert_eq!(*value, 1);
    /// ```
    #[inline(always)]
    pub unsafe fn get_unchecked(&self, key: usize) -> &T {
        #[cfg(all(feature = "strict"))]
        assert!(!self.is_free(key));

        // # Safety
        // Function invariants imply the space is occupied by an initialized value
        unsafe { &self.data.get_unchecked(key).assume_init_ref().value }
    }

    /// Provides mutable access to the value at `key`.
    ///
    /// # Returns
    ///
    /// An immutable borrow of the value at `key`.
    ///
    /// # Safety
    ///
    /// `key` must have originated from calling [`alloc`] on the same instance
    /// and the space must not already been freed since the [`alloc`] call.
    ///
    /// There must be no existing borrows of the value at `key` via [`get_unchecked`] or [`get_mut_unchecked`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
    /// let key = list.alloc(8).unwrap();
    /// let value = unsafe { list.get_mut_unchecked(key) };
    /// *value = 2;
    /// assert_eq!(unsafe { list.free_unchecked(key) }, 2);
    /// ```
    #[inline(always)]
    pub unsafe fn get_mut_unchecked(&mut self, key: usize) -> &mut T {
        #[cfg(all(feature = "strict"))]
        assert!(!self.is_free(key));

        // # Safety
        // Function invariants imply the space is occupied by an initialized value
        unsafe { &mut self.data.get_unchecked_mut(key).assume_init_mut().value }
    }

    /// Returns an upper bound on the number of elements contained.
    /// The actual number of elements is guaranteed to be less than or equal to this.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 16> = FixedFreeList::new();
    /// list.alloc(5);
    /// assert_eq!(list.size_hint(), 1);
    /// ```
    #[inline(always)]
    pub fn size_hint(&self) -> usize {
        self.high
    }

    /// Returns `true` if there is no free space left.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 1> = FixedFreeList::new();
    /// assert!(!list.is_full());
    /// list.alloc(7);
    /// assert!(list.is_full());
    /// ```
    #[inline(always)]
    pub fn is_full(&self) -> bool {
        self.high == N && self.next == N
    }

    /// Removes and drops all contained values.
    ///
    /// # Time Complexity
    ///
    /// O(1) if `T: Copy`, otherwise O(N).
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list: FixedFreeList<i32, 1> = FixedFreeList::new();
    /// list.alloc(3);
    /// assert!(list.is_full());
    /// list.clear();
    /// assert!(!list.is_full());
    /// ```
    pub fn clear(&mut self) {
        if mem::needs_drop::<T>() {
            let mut free = [false; N];
            let mut next = self.next;
            while next < N {
                free[next] = true;
                next = unsafe { self.data.get_unchecked(next).assume_init_ref().next };
            }
            for (i, &is_free) in free.iter().enumerate().take(self.high) {
                if !is_free {
                    unsafe {
                        ManuallyDrop::drop(
                            &mut self.data.get_unchecked_mut(i).assume_init_mut().value,
                        );
                    }
                }
            }
        }

        self.high = 0;
        self.next = N;
    }
}

unsafe impl<T: Sync, const N: usize> Sync for FixedFreeList<T, N> {}
unsafe impl<T: Send, const N: usize> Send for FixedFreeList<T, N> {}

impl<T, const N: usize> Drop for FixedFreeList<T, N> {
    #[inline(always)]
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            self.clear();
        }
    }
}

#[derive(Debug)]
enum Space<T: Sized> {
    Value(T),
    Free(usize),
    Uninit,
}

trait UninitProvider: Sized {
    const UNINIT: Space<Self>;
}

impl<T> UninitProvider for T {
    const UNINIT: Space<Self> = Space::Uninit;
}

impl<T, const N: usize> Debug for FixedFreeList<T, N>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result {
        // Alternative array initializer for rustc <1.63
        // let mut spaces = [<&T>::UNINIT; N];
        let mut spaces = std::array::from_fn::<Space<&T>, N, _>(|_| Space::Uninit);
        let mut next = self.next;
        while next < N {
            let free = unsafe { self.data.get_unchecked(next).assume_init_ref().next };
            spaces[next] = Space::Free(free);
            next = free;
        }
        for (i, space) in spaces.iter_mut().enumerate().take(self.high) {
            if let Space::Uninit = space {
                *space = Space::Value(unsafe { &self.data[i].assume_init_ref().value });
            }
        }

        f.debug_struct("FixedFreeList")
            .field("next", &self.next)
            .field("high", &self.high)
            .field("data", &spaces)
            .finish()
    }
}

impl<T, const N: usize> Default for FixedFreeList<T, N> {
    fn default() -> Self {
        Self::new()
    }
}

/// A lifetimed key into a `SafeFixedFreeList`
pub struct ArenaKey<'a, T> {
    index: usize,
    _marker: PhantomData<&'a T>,
}

impl<'a, T> Debug for ArenaKey<'a, T> {
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.debug_struct("ArenaKey")
            .field("index", &self.index)
            .finish()
    }
}

/// A fixed-size free-list with key lifetime safety and macroless unique typing.
/// This is a somewhat experimental use of the borrowchecker,
/// and as such [`new`] is `unsafe`.
pub struct SafeFixedFreeList<'a, T, const N: usize, U> {
    _marker: PhantomData<&'a U>,
    inner: FixedFreeList<T, N>,
}

impl<'a, T, const N: usize, U: Fn()> SafeFixedFreeList<'a, T, N, U> {
    /// Creates a new empty [`SafeFixedFreeList`]
    ///
    /// # Safety
    /// You MUST provide a unique inline closure to ensure keys are not
    /// shared with another instance.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list = unsafe { SafeFixedFreeList::<i32, 16, _>::new(||()) };
    /// ```
    #[inline(always)]
    pub unsafe fn new(_: U) -> Self {
        Self {
            _marker: PhantomData,
            inner: FixedFreeList::new(),
        }
    }

    /// If there is space, adds `value` to the free list and returns its key.
    /// If there is no space, Drops `value` and returns `None`.
    ///
    /// # Returns
    ///
    /// `None` if the list was already full.
    /// Note: `value` is dropped in this case. Check [`is_full`] beforehand to avoid this if desired.
    ///
    /// `Some(key)` if there was spare capacity to accommodate `value`.
    /// `key` can now be used to access `value` via [`get`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list = unsafe { SafeFixedFreeList::<i32, 16, _>::new(||()) };
    /// list.alloc(1);
    /// ```
    #[inline(always)]
    pub fn alloc<'k>(&mut self, value: T) -> Option<ArenaKey<'k, U>>
    where
        'a: 'k,
    {
        self.inner.alloc(value).map(|index| ArenaKey {
            index,
            _marker: PhantomData,
        })
    }

    /// Frees the space occupied by the value at `key` and returns the value.
    ///
    /// # Returns
    ///
    /// The value at `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list = unsafe { SafeFixedFreeList::<i32, 16, _>::new(||()) };
    /// let key = list.alloc(1).unwrap();
    /// let value = list.free(key);
    /// assert_eq!(value, 1);
    /// ```
    #[inline(always)]
    pub fn free(&mut self, key: ArenaKey<U>) -> T {
        unsafe { self.inner.free_unchecked(key.index) }
    }

    /// Provides immutable access to the value at `key`.
    ///
    /// # Returns
    ///
    /// An immutable borrow of the value at `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list = unsafe { SafeFixedFreeList::<i32, 16, _>::new(||()) };
    /// let key = list.alloc(1).unwrap();
    /// let value = list.get(&key);
    /// assert_eq!(*value, 1);
    /// ```
    #[inline(always)]
    pub fn get<'k: 'v, 'v>(&self, key: &'k ArenaKey<U>) -> &'v T
    where
        'a: 'k,
    {
        unsafe { mem::transmute::<&T, &T>(self.inner.get_unchecked(key.index)) }
    }

    /// Provides mutable access to the value at `key`.
    ///
    /// # Returns
    ///
    /// An immutable borrow of the value at `key`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list = unsafe { SafeFixedFreeList::<i32, 16, _>::new(||()) };
    /// let mut key = list.alloc(8).unwrap();
    /// let value = list.get_mut(&mut key);
    /// *value = 2;
    /// assert_eq!(list.free(key), 2);
    /// ```
    #[inline(always)]
    pub fn get_mut<'k: 'v, 'v>(&mut self, key: &'k mut ArenaKey<U>) -> &'v mut T
    where
        'a: 'k,
    {
        unsafe { mem::transmute::<&mut T, &mut T>(self.inner.get_mut_unchecked(key.index)) }
    }

    /// Returns an upper bound on the number of elements contained.
    /// The actual number of elements is guaranteed to be less than or equal to this.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list = unsafe { SafeFixedFreeList::<i32, 16, _>::new(||()) };
    /// list.alloc(5);
    /// assert_eq!(list.size_hint(), 1);
    /// ```
    #[inline(always)]
    pub fn size_hint(&self) -> usize {
        self.inner.size_hint()
    }

    /// Returns `true` if there is no free space left.
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list = unsafe { SafeFixedFreeList::<i32, 1, _>::new(||()) };
    /// assert!(!list.is_full());
    /// list.alloc(7);
    /// assert!(list.is_full());
    /// ```
    #[inline(always)]
    pub fn is_full(&self) -> bool {
        self.inner.is_full()
    }

    /// Removes and drops all contained values.
    ///
    /// # Time Complexity
    ///
    /// O(1) if `T: Copy`, otherwise O(N).
    ///
    /// # Examples
    ///
    /// ```
    /// # use fixed_free_list::*;
    /// let mut list = unsafe { SafeFixedFreeList::<i32, 1, _>::new(||()) };
    /// list.alloc(3);
    /// assert!(list.is_full());
    /// list.clear();
    /// assert!(!list.is_full());
    /// ```
    #[inline(always)]
    pub fn clear(&mut self) {
        self.inner.clear();
    }
}

impl<'a, T, const N: usize, U: Fn()> Debug for SafeFixedFreeList<'a, T, N, U>
where
    T: Debug,
{
    fn fmt(&self, f: &mut Formatter) -> Result {
        f.debug_struct("SafeFixedFreeList")
            .field("inner", &self.inner)
            .finish()
    }
}

#[cfg(test)]
mod test {
    use crate::*;
    use rand::Rng;
    use std::cell::RefCell;

    #[test]
    fn test_default() {
        let heap: FixedFreeList<i32, 4> = FixedFreeList::default();
        assert_eq!(0, heap.high);
    }

    #[test]
    fn test_safe() {
        fn consume<T>(_: T) {}
        let mut list = unsafe { SafeFixedFreeList::<u32, 4, _>::new(|| ()) };
        assert_eq!(0, list.size_hint());
        let mut key1 = list.alloc(5).unwrap();
        let mut key2 = list.alloc(6).unwrap();
        assert_eq!(2, list.size_hint());
        let value1 = list.get_mut(&mut key1);
        let value2 = list.get_mut(&mut key2);
        // miri hates this, I think its a valid abuse of borrowck though
        *value1 = 2;
        consume(value1);
        consume(value2);
        assert_eq!(&2, list.get(&key1));
        assert_eq!(&6, list.get(&key2));
        assert!(!list.is_full());
        assert_eq!(format!("{:?}", key1), "ArenaKey { index: 0 }");
        list.free(key1);
        list.free(key2);
        assert_eq!(2, list.size_hint());
        assert_eq!(format!("{:?}", list), "SafeFixedFreeList { inner: FixedFreeList { next: 1, high: 2, data: [Free(4), Free(0), Uninit, Uninit] } }");
        list.clear();
        assert_eq!(0, list.size_hint());
        consume(list);
    }

    #[test]
    fn test_get_unchecked() {
        let mut list = FixedFreeList::<usize, 16>::new();
        for i in 0..16 {
            assert_eq!(list.alloc(i), Some(i));
        }
        for i in 0..16 {
            unsafe {
                assert_eq!(list.get_unchecked(i), &i);
            }
        }
        for i in 0..16 {
            unsafe {
                *list.get_mut_unchecked(i) = i * 2;
            }
        }
        for i in 0..16 {
            unsafe {
                assert_eq!(list.get_unchecked(i), &(i * 2));
            }
        }
        assert!(list.is_full());
    }

    #[test]
    fn test_remove_all() {
        let mut list = FixedFreeList::<usize, 16>::new();
        for i in 0..16 {
            assert_eq!(list.alloc(i), Some(i));
        }
        for i in 0..16 {
            unsafe {
                assert_eq!(list.free_unchecked(i), i);
            }
        }
        for i in 0..17 {
            assert!(list.is_free(i));
        }
        for i in 0..16 {
            list.alloc(i);
        }
        assert!(list.is_full());
    }

    #[test]
    fn test_reuse_half() {
        let mut list = FixedFreeList::<usize, 16>::new();
        for i in 0..16 {
            assert_eq!(list.alloc(i), Some(i));
        }
        for i in 0..8 {
            unsafe {
                list.free_unchecked(i * 2);
            }
        }
        for i in 0..8 {
            list.alloc(i);
        }
        assert!(list.is_full());
    }

    #[test]
    fn test_reuse_preferred() {
        let mut list = FixedFreeList::<u32, 16>::new();
        for i in 0..8 {
            assert_eq!(list.alloc(i), Some(i as usize));
        }
        for i in 0..4 {
            unsafe {
                list.free_unchecked(i * 2usize);
            }
        }
        for i in 0..4 {
            list.alloc(i);
        }
        assert_eq!(list.size_hint(), 8);
        for i in 8..16 {
            assert_eq!(list.alloc(i), Some(i as usize));
        }
        assert!(list.is_full());
    }

    #[test]
    fn test_debug() {
        let mut list = FixedFreeList::<u32, 8>::new();
        list.alloc(3);
        let key1 = list.alloc(5).unwrap();
        list.alloc(7);
        list.alloc(4);
        let key2 = list.alloc(2).unwrap();
        unsafe {
            list.free_unchecked(key1);
            list.free_unchecked(key2);
        }
        assert_eq!(format!("{:?}", list), "FixedFreeList { next: 4, high: 5, data: [Value(3), Free(8), Value(7), Value(4), Free(1), Uninit, Uninit, Uninit] }");
    }

    #[test]
    fn test_full() {
        let mut list = FixedFreeList::<u32, 4>::new();
        assert_eq!(list.alloc(3), Some(0));
        assert_eq!(list.alloc(5), Some(1));
        assert_eq!(list.alloc(7), Some(2));
        assert_eq!(list.alloc(4), Some(3));
        assert_eq!(list.alloc(2), None);
    }

    #[test]
    fn test_drop() {
        let drops = RefCell::new(0usize);
        {
            let mut list: FixedFreeList<DropCounted, 16> = FixedFreeList::new();
            for _ in 0..11 {
                list.alloc(DropCounted(&drops));
            }
            assert_eq!(*drops.borrow(), 0);

            // Drop a few
            for i in 0..4 {
                unsafe {
                    list.free_unchecked(i);
                }
            }
            assert_eq!(*drops.borrow(), 4);

            // Let the rest drop
        }
        assert_eq!(*drops.borrow(), 11);
        {
            let mut list: FixedFreeList<DropCounted, 1> = FixedFreeList::new();
            list.alloc(DropCounted(&drops));

            // Inserting into a full list should drop the value
            list.alloc(DropCounted(&drops));
            assert_eq!(*drops.borrow(), 12);

            // Let the rest drop
        }
        assert_eq!(*drops.borrow(), 13);
    }

    struct DropCounted<'a>(&'a RefCell<usize>);

    impl<'a> Drop for DropCounted<'a> {
        fn drop(&mut self) {
            *self.0.borrow_mut() += 1;
        }
    }

    #[test]
    fn test_fuzz() {
        fuzz::<0, 4>(10);
        fuzz::<1, 8>(10);
        fuzz::<2, 8>(10);
        fuzz::<3, 8>(10);
        fuzz::<5, 8>(10);
        fuzz::<7, 16>(10);
        fuzz::<16, 16>(10);
        fuzz::<16, 64>(10);
    }

    fn fuzz<const N: usize, const M: usize>(iters: usize) {
        for _ in 0..iters {
            let mut list: FixedFreeList<usize, N> = FixedFreeList::new();
            let mut keys = Vec::new();
            let mut count = 0;
            let mut high = 0;
            for i in 0..M {
                if rand::thread_rng().gen() {
                    if let Some(key) = list.alloc(i) {
                        keys.push(key);
                        count += 1;
                        if high < count {
                            high = count;
                        }
                    } else {
                        assert_eq!(count, N);
                    }
                } else if count > 0 {
                    let key = keys.swap_remove(rand::thread_rng().gen_range(0..keys.len()));
                    unsafe {
                        assert!(!list.is_free(key));
                        list.free_unchecked(key);
                        assert!(list.is_free(key));
                        count -= 1;
                    }
                }
                assert_eq!(list.size_hint(), high);
            }
        }
    }
}

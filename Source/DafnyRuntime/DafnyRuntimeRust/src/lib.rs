#![allow(clippy::collapsible_else_if)]
#![allow(clippy::multiple_bound_locations)]
#![allow(clippy::missing_safety_doc)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::clone_on_copy)]
#![warn(
    absolute_paths_not_starting_with_crate,
    explicit_outlives_requirements,
    deprecated_in_future,
    keyword_idents,
    let_underscore_drop,
    macro_use_extern_crate,
    // missing_debug_implementations,
    non_ascii_idents,
    noop_method_call,
    rust_2021_incompatible_closure_captures,
    rust_2021_incompatible_or_patterns,
    rust_2021_prefixes_incompatible_syntax,
    rust_2021_prelude_collisions,
    rust_2018_idioms,
    single_use_lifetimes,
    trivial_numeric_casts,
    unit_bindings,
    unreachable_pub,
    unsafe_op_in_unsafe_fn,
    unused_extern_crates,
    unused_lifetimes,
    unused_qualifications,
)]

#[cfg(test)]
mod tests;

mod system;
pub use mem::MaybeUninit;
use num::{One, Signed};
pub use once_cell::unsync::Lazy;
use std::{
    borrow::Borrow,
    boxed::Box,
    clone::Clone,
    cmp::Ordering,
    collections::{HashMap, HashSet},
    convert::From,
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
    mem,
    ops::{Add, Deref, Fn, Sub},
    ptr::NonNull,
    vec::Vec,
};

#[cfg(not(feature = "small-int"))]
mod big_int;
#[cfg(not(feature = "small-int"))]
pub use big_int::*;

#[cfg(feature = "small-int")]
mod small_int;
#[cfg(feature = "small-int")]
pub use small_int::*;

#[cfg(not(feature = "sync"))]
pub use ::std::{
    cell::RefCell,
    rc::{Rc, Weak},
};

#[cfg(feature = "sync")]
pub use ::std::sync::{Arc as Rc, Mutex as RefCell, Weak};

pub use system::*;

pub use itertools;
pub use num::FromPrimitive;
pub use num::NumCast;
pub use num::ToPrimitive;
pub use num::Zero;
pub use std::convert::Into;

pub use ::std::any::Any;
pub use ::std::marker::Send;
pub use ::std::marker::Sync;

#[cfg(not(feature = "sync"))]
pub type DynAny = dyn Any;
#[cfg(feature = "sync")]
pub type DynAny = dyn Any + Send + Sync;

#[cfg(not(feature = "sync"))]
pub use ::std::cell::UnsafeCell;

#[cfg(feature = "sync")]
pub struct UnsafeCell<T: ?Sized> {
    data: ::std::cell::UnsafeCell<T>, // UnsafeCell for interior mutability
}
// SAFETY: UnsafeCell is not possibly sync normally.
// However, we use it only for raw pointers, and fields and access to read and write
// to fields will be subject to mutexes in any cases.
#[cfg(feature = "sync")]
unsafe impl<T: ?Sized> Sync for UnsafeCell<T> where T: Send {}
#[cfg(feature = "sync")]
impl<T: Sized> UnsafeCell<T> {
    pub fn new(data: T) -> Self {
        UnsafeCell {
            data: ::std::cell::UnsafeCell::new(data),
        }
    }
}
#[cfg(feature = "sync")]
impl<T: ?Sized> UnsafeCell<T> {
    pub fn get(&self) -> *mut T {
        ::std::cell::UnsafeCell::get(&self.data)
    }
    pub fn raw_get(this: *const UnsafeCell<T>) -> *mut T {
        unsafe { ::std::cell::UnsafeCell::raw_get(&(*this).data) }
    }
}

// An atomic box is just a RefCell in Rust
pub type SizeT = usize;

#[cfg(not(feature = "sync"))]
pub trait DafnyType: Clone + DafnyPrint + 'static {}
#[cfg(feature = "sync")]
pub trait DafnyType: Clone + DafnyPrint + Send + Sync + 'static {}

#[cfg(not(feature = "sync"))]
impl<T> DafnyType for T where T: Clone + DafnyPrint + 'static {}
#[cfg(feature = "sync")]
impl<T> DafnyType for T where T: Clone + DafnyPrint + Send + Sync + 'static {}

pub trait DafnyTypeEq: DafnyType + Hash + Eq {}

impl<T> DafnyTypeEq for T where T: DafnyType + Hash + Eq {}

// Dafny's type (0) compiles to NontrivialDefault to prevent subset types from being considered as Default if their witness is nonzero
pub trait NontrivialDefault {
    fn nontrivial_default() -> Self;
}

pub mod dafny_runtime_conversions {
    use crate::DafnyType;
    use crate::DafnyTypeEq;
    pub type DafnyInt = crate::DafnyInt;
    pub type DafnySequence<T> = crate::Sequence<T>;
    pub type DafnyMap<K, V> = crate::Map<K, V>;
    pub type DafnySet<T> = crate::Set<T>;
    pub type DafnyMultiset<T> = crate::Multiset<T>;
    pub type DafnyBool = bool;
    pub type DafnyChar = crate::DafnyChar;
    pub type DafnyCharUTF16 = crate::DafnyCharUTF16;

    use ::std::collections::HashMap;
    use ::std::collections::HashSet;
    use ::std::hash::Hash;

    pub use super::Rc;

    pub mod object {
        pub use super::Rc;
        pub type DafnyClass<T> = crate::Object<T>;
        pub type DafnyArray<T> = crate::Object<[T]>;
        pub type DafnyArray2<T> = crate::Object<crate::Array2<T>>;
        pub type DafnyArray3<T> = crate::Object<crate::Array3<T>>;
        // Conversion to and from Dafny reference-counted classes. All these methods take ownership of the class.
        pub fn dafny_class_to_struct<T: Clone>(ptr: DafnyClass<T>) -> T {
            let t: &T = crate::rd!(ptr);
            t.clone()
        }
        pub fn dafny_class_to_boxed_struct<T: Clone>(ptr: DafnyClass<T>) -> Box<T> {
            Box::new(dafny_class_to_struct(ptr))
        }
        pub unsafe fn dafny_class_to_rc_struct<T: Clone>(ptr: DafnyClass<T>) -> Rc<T> {
            unsafe { crate::rcmut::to_rc(ptr.0.unwrap()) }
        }
        pub fn struct_to_dafny_class<T>(t: T) -> DafnyClass<T> {
            crate::Object::new(t)
        }
        pub fn boxed_struct_to_dafny_class<T>(t: Box<T>) -> DafnyClass<T> {
            struct_to_dafny_class(*t)
        }
        pub unsafe fn rc_struct_to_dafny_class<T: ?Sized>(t: Rc<T>) -> DafnyClass<T> {
            unsafe { crate::Object::from_rc(t) }
        }
        // Conversions to and from Dafny arrays. They all take ownership
        pub unsafe fn dafny_array_to_vec<T: Clone>(ptr: DafnyArray<T>) -> Vec<T> {
            ptr.as_ref().to_vec()
        }
        pub fn vec_to_dafny_array<T: Clone>(array: Vec<T>) -> DafnyArray<T> {
            // SAFETY: We own the array
            unsafe { crate::Object::from_rc(Rc::from(array.into_boxed_slice())) }
        }
        pub unsafe fn dafny_array2_to_vec<T: Clone>(ptr: DafnyArray2<T>) -> Vec<Vec<T>> {
            crate::rd!(ptr).to_vec()
        }
    }

    pub mod ptr {
        pub use super::Rc;
        pub type DafnyClass<T> = crate::Ptr<T>;
        pub type DafnyArray<T> = crate::Ptr<[T]>;
        pub type DafnyArray2<T> = crate::Ptr<crate::Array2<T>>;
        pub type DafnyArray3<T> = crate::Ptr<crate::Array3<T>>;
        // Conversion to and from Dafny reference-counted classes. All these methods take ownership of the class.
        pub unsafe fn dafny_class_to_struct<T: Clone>(ptr: DafnyClass<T>) -> T {
            unsafe { *dafny_class_to_boxed_struct(ptr) }
        }
        pub unsafe fn dafny_class_to_boxed_struct<T: Clone>(ptr: DafnyClass<T>) -> Box<T> {
            unsafe { Box::from_raw(crate::Ptr::into_raw(ptr)) }
        }
        pub fn struct_to_dafny_class<T>(t: T) -> DafnyClass<T> {
            boxed_struct_to_dafny_class(Box::new(t))
        }
        pub fn boxed_struct_to_dafny_class<T>(t: Box<T>) -> DafnyClass<T> {
            crate::Ptr::from_raw_nonnull(Box::into_raw(t))
        }
        // Conversions to and from Dafny arrays. They all take ownership
        pub unsafe fn dafny_array_to_vec<T: Clone>(ptr: DafnyArray<T>) -> Vec<T> {
            ptr.as_ref().to_vec()
        }
        pub fn vec_to_dafny_array<T: Clone>(array: Vec<T>) -> DafnyArray<T> {
            crate::Ptr::from_box(array.into_boxed_slice())
        }
        pub unsafe fn dafny_array2_to_vec<T: Clone>(ptr: DafnyArray2<T>) -> Vec<Vec<T>> {
            unsafe { Box::from_raw(crate::Ptr::into_raw(ptr)).to_vec() }
        }
    }

    pub fn dafny_sequence_to_vec<T, X>(s: &DafnySequence<T>, elem_converter: fn(&T) -> X) -> Vec<X>
    where
        T: DafnyType,
    {
        let mut array: Vec<T> = Vec::with_capacity(s.cardinality_usize());
        DafnySequence::<T>::append_recursive(&mut array, s);
        array.iter().map(elem_converter).collect()
    }

    // Used for external conversions
    pub fn vec_to_dafny_sequence<T, X>(
        array: &Vec<X>,
        elem_converter: fn(&X) -> T,
    ) -> DafnySequence<T>
    where
        T: DafnyType,
    {
        let mut result: Vec<T> = Vec::with_capacity(array.len());
        for elem in array.iter() {
            result.push(elem_converter(elem));
        }
        DafnySequence::<T>::from_array_owned(result)
    }

    pub fn dafny_map_to_hashmap<K, V, K2, V2>(
        m: &DafnyMap<K, V>,
        converter_k: fn(&K) -> K2,
        converter_v: fn(&V) -> V2,
    ) -> HashMap<K2, V2>
    where
        K: DafnyTypeEq,
        V: DafnyTypeEq,
        K2: Eq + Hash,
        V2: Clone,
    {
        m.to_hashmap_owned(converter_k, converter_v)
    }

    pub fn hashmap_to_dafny_map<K2, V2, K, V>(
        map: &HashMap<K2, V2>,
        converter_k: fn(&K2) -> K,
        converter_v: fn(&V2) -> V,
    ) -> DafnyMap<K, V>
    where
        K: DafnyTypeEq,
        V: DafnyTypeEq,
        K2: Eq + Hash,
        V2: Clone,
    {
        DafnyMap::<K, V>::from_hashmap(map, converter_k, converter_v)
    }

    // --unicode-char:true
    pub mod unicode_chars_true {
        use crate::Sequence;

        type DafnyChar = crate::DafnyChar;
        type DafnyString = Sequence<DafnyChar>;

        pub fn string_to_dafny_string(s: &str) -> DafnyString {
            Sequence::from_array_owned(s.chars().map(crate::DafnyChar).collect())
        }
        pub fn dafny_string_to_string(s: &DafnyString) -> String {
            let characters = s.to_array();
            characters.iter().map(|v| v.0).collect::<String>()
        }
    }

    // --unicode-char:false
    pub mod unicode_chars_false {
        use crate::Sequence;

        type DafnyCharUTF16 = crate::DafnyCharUTF16;
        type DafnyString = Sequence<DafnyCharUTF16>;

        pub fn string_to_dafny_string(s: &str) -> DafnyString {
            Sequence::from_array_owned(s.encode_utf16().map(crate::DafnyCharUTF16).collect())
        }
        pub fn dafny_string_to_string(s: &DafnyString) -> String {
            let characters = s
                .to_array()
                .as_ref()
                .iter()
                .map(|v| v.0)
                .collect::<Vec<_>>();
            String::from_utf16_lossy(&characters)
        }
    }

    pub fn set_to_dafny_set<U, T: DafnyTypeEq>(
        set: &HashSet<U>,
        converter: fn(&U) -> T,
    ) -> DafnySet<T> {
        DafnySet::from_iterator(set.iter().map(converter))
    }
    pub fn dafny_set_to_set<T, U>(set: &DafnySet<T>, converter: fn(&T) -> U) -> HashSet<U>
    where
        T: DafnyTypeEq,
        U: Clone + Eq + Hash,
    {
        let mut result: HashSet<U> = HashSet::new();
        for s in set.data.iter() {
            result.insert(converter(s));
        }
        result
    }

    pub fn dafny_multiset_to_owned_vec<T, U>(
        ms: &DafnyMultiset<T>,
        converter: fn(&T) -> U,
    ) -> Vec<U>
    where
        T: DafnyTypeEq,
        U: Clone + Eq,
    {
        let mut result: Vec<U> = Vec::new();
        for s in ms.data.iter() {
            // Push T as many times as its size
            for _ in 0..s.1.as_usize() {
                result.push(converter(s.0));
            }
        }
        result
    }

    pub fn vec_to_dafny_multiset<T, U>(vec: &Vec<U>, converter: fn(&U) -> T) -> DafnyMultiset<T>
    where
        T: DafnyTypeEq,
        U: Clone + Eq + Hash,
    {
        DafnyMultiset::from_iterator(vec.iter().map(|u: &U| converter(u)))
    }
}

pub trait DafnyUsize {
    fn into_usize(self) -> usize;
}

// **************
// Dafny integers
// **************

impl DafnyInt {
    pub fn as_usize(&self) -> usize {
        self.to_usize().unwrap()
    }
}

impl DafnyUsize for DafnyInt {
    fn into_usize(self) -> usize {
        self.as_usize()
    }
}

// truncate_u(x, u64)
// = <DafnyInt as ToPrimitive>::to_u128(&x).unwrap() as u64;
#[macro_export]
macro_rules! truncate {
    ($x:expr, $t:ty) => {
        <$crate::DafnyInt as ::std::convert::Into<$t>>::into($x)
    };
}

impl NontrivialDefault for DafnyInt {
    fn nontrivial_default() -> Self {
        Self::default()
    }
}

impl From<&[u8]> for DafnyInt {
    fn from(number: &[u8]) -> Self {
        DafnyInt::parse_bytes(number, 10)
    }
}

// Now the same but for &[u8, N] for any kind of such references
impl<const N: usize> From<&[u8; N]> for DafnyInt {
    fn from(number: &[u8; N]) -> Self {
        DafnyInt::parse_bytes(number, 10)
    }
}

impl From<char> for DafnyInt {
    fn from(c: char) -> Self {
        let cu32: u32 = c.into();
        int!(cu32)
    }
}

impl From<DafnyChar> for DafnyInt {
    fn from(c: DafnyChar) -> Self {
        int!(c.0)
    }
}

impl From<DafnyCharUTF16> for DafnyInt {
    fn from(c: DafnyCharUTF16) -> Self {
        int!(c.0)
    }
}

// **************
// Immutable sequences
// **************

impl<T: DafnyTypeEq> Eq for Sequence<T> {}

impl<T: DafnyType> Add<&Sequence<T>> for &Sequence<T> {
    type Output = Sequence<T>;

    fn add(self, rhs: &Sequence<T>) -> Self::Output {
        Sequence::new_concat_sequence(self, rhs)
    }
}

impl<T: DafnyType + Hash> Hash for Sequence<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.cardinality_usize().hash(state);
        let array = self.to_array();
        // Iterate over the elements
        for elt in array.iter() {
            elt.hash(state);
        }
    }
}

// Clone can be derived automatically
#[derive(Clone)]
pub enum Sequence<T>
where
    T: DafnyType,
{
    ArraySequence {
        // Values could be a native array because we will know statically that all
        // accesses are in bounds when using this data structure
        values: Rc<Vec<T>>,
    },
    ConcatSequence {
        left: Rc<RefCell<Sequence<T>>>,
        right: Rc<RefCell<Sequence<T>>>,
        length: SizeT,
        cache: Rc<RefCell<Option<Rc<Vec<T>>>>>,
    },
}

impl<T> Sequence<T>
where
    T: DafnyType,
{
    pub fn from_array(values: Ptr<[T]>) -> Sequence<T> {
        let mut v = vec![];
        v.extend_from_slice(read!(values));
        Sequence::ArraySequence { values: Rc::new(v) }
    }
    pub fn from_array_object(values: &Object<[T]>) -> Sequence<T> {
        let mut v = vec![];
        v.extend_from_slice(rd!(values));
        Sequence::ArraySequence { values: Rc::new(v) }
    }
    pub fn from_array_slice(values: Ptr<[T]>, start: &DafnyInt, end: &DafnyInt) -> Sequence<T> {
        let mut v = vec![];
        v.extend_from_slice(&read!(values)[start.to_usize().unwrap()..end.to_usize().unwrap()]);
        Sequence::ArraySequence { values: Rc::new(v) }
    }
    pub fn from_array_slice_object(
        values: &Object<[T]>,
        start: &DafnyInt,
        end: &DafnyInt,
    ) -> Sequence<T> {
        let mut v = vec![];
        v.extend_from_slice(&rd!(values)[start.to_usize().unwrap()..end.to_usize().unwrap()]);
        Sequence::ArraySequence { values: Rc::new(v) }
    }
    pub fn from_array_take(values: Ptr<[T]>, n: &DafnyInt) -> Sequence<T> {
        let mut v = vec![];
        v.extend_from_slice(&read!(values)[..n.to_usize().unwrap()]);
        Sequence::ArraySequence { values: Rc::new(v) }
    }
    pub fn from_array_take_object(values: &Object<[T]>, n: &DafnyInt) -> Sequence<T> {
        let mut v = vec![];
        v.extend_from_slice(&rd!(values)[..n.to_usize().unwrap()]);
        Sequence::ArraySequence { values: Rc::new(v) }
    }
    pub fn from_array_drop(values: Ptr<[T]>, n: &DafnyInt) -> Sequence<T> {
        let mut v = vec![];
        v.extend_from_slice(&read!(values)[n.to_usize().unwrap()..]);
        Sequence::ArraySequence { values: Rc::new(v) }
    }
    pub fn from_array_drop_object(values: &Object<[T]>, n: &DafnyInt) -> Sequence<T> {
        let mut v = vec![];
        v.extend_from_slice(&rd!(values)[n.to_usize().unwrap()..]);
        Sequence::ArraySequence { values: Rc::new(v) }
    }
    pub fn from_array_owned(values: Vec<T>) -> Sequence<T> {
        Sequence::ArraySequence {
            values: Rc::new(values),
        }
    }
    pub(crate) fn new_concat_sequence(left: &Sequence<T>, right: &Sequence<T>) -> Sequence<T> {
        Sequence::ConcatSequence {
            left: Rc::new(RefCell::new(left.clone())),
            right: Rc::new(RefCell::new(right.clone())),
            length: left.cardinality_usize() + right.cardinality_usize(),
            cache: Rc::new(RefCell::new(None)),
        }
    }
    pub fn to_array(&self) -> Rc<Vec<T>> {
        // Let's convert the if then else below to a proper match statement
        match self {
            Sequence::ArraySequence { values, .. } =>
            // The length of the elements
            {
                Rc::clone(values)
            }
            Sequence::ConcatSequence {
                length,
                cache,
                left,
                right,
            } => {
                #[cfg(feature = "sync")]
                {
                    let guard = cache.as_ref().lock().unwrap();
                    let cache_borrow: Option<&Rc<Vec<T>>> = guard.as_ref();
                    if let Some(cache) = cache_borrow {
                        return Rc::clone(cache);
                    }
                }

                #[cfg(not(feature = "sync"))]
                {
                    let cache_opened = cache.as_ref().clone();
                    let cache_opened_borrowed = cache_opened.borrow();
                    let cache_borrow: Option<&Rc<Vec<T>>> = cache_opened_borrowed.as_ref();
                    if let Some(cache) = cache_borrow {
                        return Rc::clone(cache);
                    }
                }
                // Let's create an array of size length and fill it up recursively
                // We don't materialize nested arrays because most of the time they are forgotten
                let mut array: Vec<T> = Vec::with_capacity(*length);
                Sequence::<T>::append_recursive(&mut array, self);
                let result = Rc::new(array);
                #[cfg(not(feature = "sync"))]
                {
                    *left.borrow_mut() = seq!();
                    *right.borrow_mut() = seq!();
                }
                #[cfg(feature = "sync")]
                {
                    let mut left_guard = left.as_ref().lock().unwrap();
                    let mut right_guard = right.as_ref().lock().unwrap();
                    *left_guard = seq!();
                    *right_guard = seq!();
                }
                #[cfg(not(feature = "sync"))]
                let mut guard = cache.borrow_mut();
                #[cfg(feature = "sync")]
                let mut guard = cache.as_ref().lock().unwrap();
                *guard = Some(result.clone());
                result
            }
        }
    }

    pub fn append_simple(array: &mut Vec<T>, this: &Sequence<T>) -> bool {
        match this {
            Sequence::ArraySequence { values, .. } => {
                for value in values.iter() {
                    array.push(value.clone());
                }
                true
            }
            _ => false,
        }
    }

    pub fn append_recursive(array: &mut Vec<T>, this: &Sequence<T>) {
        let mut this_ptr: *const Sequence<T> = this;
        loop {
            // SAFETY: The invariant is that this_ptr is always a pointer to a sub-sequence of the original `this`parameter when following the field name 'right', which are allocated in this scope
            match unsafe { &*this_ptr } {
                Sequence::ArraySequence { values, .. } => {
                    for value in values.iter() {
                        array.push(value.clone());
                    }
                    return;
                }
                Sequence::ConcatSequence {
                    cache: boxed,
                    left,
                    right,
                    ..
                } =>
                // Let's create an array of size length and fill it up recursively
                {
                    #[cfg(feature = "sync")]
                    let into_boxed = boxed.as_ref();
                    #[cfg(feature = "sync")]
                    let into_boxed_borrowed = into_boxed;
                    #[cfg(feature = "sync")]
                    let guard = into_boxed_borrowed.lock().unwrap();
                    #[cfg(feature = "sync")]
                    let borrowed: Option<&Rc<Vec<T>>> = guard.as_ref();

                    #[cfg(not(feature = "sync"))]
                    let into_boxed = boxed.as_ref().clone();
                    #[cfg(not(feature = "sync"))]
                    let into_boxed_borrowed = into_boxed.borrow();
                    #[cfg(not(feature = "sync"))]
                    let borrowed: Option<&Rc<Vec<T>>> = into_boxed_borrowed.as_ref();
                    if let Some(values) = borrowed.as_ref() {
                        for value in values.iter() {
                            array.push(value.clone());
                        }
                        return;
                    }
                    #[cfg(not(feature = "sync"))]
                    {
                        let left_empty = left.as_ref().borrow().cardinality_usize() == 0;
                        let right_empty = right.as_ref().borrow().cardinality_usize() == 0;
                        if left_empty && right_empty {
                            return;
                        } else if left_empty {
                            this_ptr = right.as_ref().as_ptr();
                        } else if right_empty {
                            this_ptr = left.as_ref().as_ptr();
                        } else {
                            if !Sequence::<T>::append_simple(array, &left.as_ref().borrow()) {
                                Sequence::<T>::append_recursive(array, &left.as_ref().borrow());
                            }
                            this_ptr = right.as_ref().as_ptr();
                        }
                    }
                    #[cfg(feature = "sync")]
                    {
                        let left_guard = left.as_ref().lock().unwrap();
                        let right_guard = right.as_ref().lock().unwrap();
                        let left_empty: bool = left_guard.cardinality_usize() == 0;
                        let right_empty: bool = right_guard.cardinality_usize() == 0;
                        if left_empty && right_empty {
                            return;
                        } else if left_empty {
                            this_ptr = right_guard.deref();
                        } else if right_empty {
                            this_ptr = left_guard.deref();
                        } else {
                            if !Sequence::<T>::append_simple(array, &left_guard) {
                                Sequence::<T>::append_recursive(array, &left_guard);
                            }
                            this_ptr = right_guard.deref();
                        }
                    }
                }
            }
        }
    }
    /// Returns the cardinality or length of this [`Sequence<T>`].
    pub fn cardinality_usize(&self) -> SizeT {
        match self {
            Sequence::ArraySequence { values, .. } =>
            // The length of the elements
            {
                values.len()
            }
            Sequence::ConcatSequence { length, .. } => *length,
        }
    }
    pub fn cardinality(&self) -> DafnyInt {
        DafnyInt::from_usize(self.cardinality_usize())
    }
    pub fn get_usize(&self, index: SizeT) -> T {
        let array = self.to_array();
        array[index].clone()
    }

    pub fn slice(&self, start: &DafnyInt, end: &DafnyInt) -> Sequence<T> {
        let start_index = start.as_usize();
        let end_index = end.as_usize();
        Sequence::from_array_owned(self.to_array()[start_index..end_index].to_vec())
    }
    pub fn take(&self, end: &DafnyInt) -> Sequence<T> {
        let end_index = end.as_usize();
        Sequence::from_array_owned(self.to_array()[..end_index].to_vec())
    }
    pub fn drop(&self, start: &DafnyInt) -> Sequence<T> {
        let start_index = start.as_usize();
        Sequence::from_array_owned(self.to_array()[start_index..].to_vec())
    }

    pub fn update_index(&self, index: &DafnyInt, value: &T) -> Self {
        let mut result = self.to_array().as_ref().clone();
        result[index.as_usize()] = value.clone();
        Sequence::from_array_owned(result)
    }

    pub fn concat(&self, other: &Sequence<T>) -> Sequence<T> {
        Sequence::new_concat_sequence(self, other)
    }

    pub fn get(&self, index: &DafnyInt) -> T {
        self.get_usize(index.as_usize())
    }
    pub fn iter(&self) -> SequenceIter<T> {
        SequenceIter {
            array: self.to_array(),
            index: 0,
        }
    }
}

pub struct SequenceIter<T: Clone> {
    array: Rc<Vec<T>>,
    index: SizeT,
}
impl<T: Clone> Iterator for SequenceIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.index < self.array.len() {
            let result = self.array[self.index].clone();
            self.index += 1;
            Some(result)
        } else {
            None
        }
    }
}

impl<T: DafnyType> Default for Sequence<T> {
    fn default() -> Self {
        Sequence::from_array_owned(vec![])
    }
}
impl<T: DafnyType> NontrivialDefault for Sequence<T> {
    fn nontrivial_default() -> Self {
        Self::default()
    }
}

impl<T: DafnyTypeEq> Sequence<T> {
    pub fn as_dafny_multiset(&self) -> Multiset<T> {
        Multiset::from_array(&self.to_array())
    }
}

// Makes it possible to write iterator.collect::<Sequence<T>> and obtain a sequence
impl<T: DafnyType> FromIterator<T> for Sequence<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Sequence::from_array_owned(iter.into_iter().collect())
    }
}

impl<T: DafnyTypeEq> Sequence<T> {
    pub fn contains(&self, value: &T) -> bool {
        self.to_array().contains(value)
    }
}
impl<T> PartialEq<Sequence<T>> for Sequence<T>
where
    T: DafnyType + PartialEq<T>,
{
    fn eq(&self, other: &Sequence<T>) -> bool {
        // Iterate through both elements and verify that they are equal
        let values: Rc<Vec<T>> = self.to_array();
        if other.cardinality_usize() != values.len() {
            return false;
        }
        for (i, value) in values.iter().enumerate() {
            if value != &other.get_usize(i) {
                return false;
            }
        }
        true
    }
}

impl<T: DafnyTypeEq> PartialOrd for Sequence<T> {
    fn partial_cmp(&self, other: &Sequence<T>) -> Option<Ordering> {
        // Comparison is only prefix-based
        match self.cardinality_usize().cmp(&other.cardinality_usize()) {
            Ordering::Equal => {
                if self == other {
                    Some(Ordering::Equal)
                } else {
                    None
                }
            }
            Ordering::Less => {
                for i in 0..self.cardinality_usize() {
                    if self.get_usize(i) != other.get_usize(i) {
                        return None;
                    }
                }
                Some(Ordering::Less)
            }
            Ordering::Greater => {
                for i in 0..other.cardinality_usize() {
                    if self.get_usize(i) != other.get_usize(i) {
                        return None;
                    }
                }
                Some(Ordering::Greater)
            }
        }
    }
}

impl<V: DafnyType> DafnyPrint for Sequence<V> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        if !V::is_char() {
            write!(f, "[")?;
        }
        let mut first = true;
        for value in self.to_array().iter() {
            if !first && !V::is_char() {
                write!(f, ", ")?;
            }
            first = false;
            value.fmt_print(f, true)?;
        }
        if !V::is_char() {
            write!(f, "]")
        } else {
            write!(f, "")
        }
    }
}

impl<V: DafnyType> Debug for Sequence<V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_print(f, false)
    }
}

// **************
// Immutable maps
// **************

#[derive(Clone)]
pub struct Map<K, V>
where
    K: DafnyTypeEq,
    V: DafnyType,
{
    data: Rc<HashMap<K, V>>,
}

impl<K: DafnyTypeEq, V: DafnyType> Default for Map<K, V> {
    fn default() -> Self {
        Map {
            data: Rc::new(HashMap::new()),
        }
    }
}

impl<K: DafnyTypeEq, V: DafnyType> NontrivialDefault for Map<K, V> {
    fn nontrivial_default() -> Self {
        Self::default()
    }
}

impl<K: DafnyTypeEq, V: DafnyType> Hash for Map<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.data.len().hash(state); // Worst performance for things that are not hashable like maps
    }
}

impl<K, V> PartialEq<Map<K, V>> for Map<K, V>
where
    K: DafnyTypeEq,
    V: DafnyTypeEq,
{
    fn eq(&self, other: &Map<K, V>) -> bool {
        if self.data.len() != other.data.len() {
            return false;
        }
        for (k, v) in self.data.iter() {
            if other.data.get(k) != Some(v) {
                return false;
            }
        }
        true
    }
}

impl<K: DafnyTypeEq, V: DafnyTypeEq> Eq for Map<K, V> {}

impl<K: DafnyTypeEq, V: DafnyType> Map<K, V> {
    pub fn new_empty() -> Map<K, V> {
        Map {
            data: Rc::new(HashMap::new()),
        }
    }
    pub fn from_array(values: &Vec<(K, V)>) -> Map<K, V> {
        Self::from_iterator(values.iter().map(|(k, v)| (k.clone(), v.clone())))
    }
    pub fn from_iterator<I>(data: I) -> Map<K, V>
    where
        I: Iterator<Item = (K, V)>,
    {
        let mut result: HashMap<K, V> = HashMap::new();
        for (k, v) in data {
            result.insert(k, v);
        }
        Self::from_hashmap_owned(result)
    }
    pub fn from_hashmap_owned(values: HashMap<K, V>) -> Map<K, V> {
        Map {
            data: Rc::new(values),
        }
    }
    pub fn to_hashmap_owned<K2, V2>(
        &self,
        converter_k: fn(&K) -> K2,
        converter_v: fn(&V) -> V2,
    ) -> HashMap<K2, V2>
    where
        K2: Eq + Hash,
        V2: Clone,
    {
        let mut result: HashMap<K2, V2> = HashMap::new();
        for (k, v) in self.data.iter() {
            result.insert(converter_k(k), converter_v(v));
        }
        result
    }
    pub fn cardinality_usize(&self) -> usize {
        self.data.len()
    }
    pub fn cardinality(&self) -> DafnyInt {
        DafnyInt::from_usize(self.cardinality_usize())
    }
    pub fn contains(&self, key: &K) -> bool {
        self.data.contains_key(key)
    }
    pub fn get_or_none(&self, key: &K) -> Option<V> {
        self.data.get(key).cloned()
    }
    // Dafny will normally guarantee that the key exists.
    pub fn get(&self, key: &K) -> V {
        self.data[key].clone()
    }
    pub fn merge(&self, other: &Map<K, V>) -> Map<K, V> {
        if other.cardinality_usize() == 0 {
            return self.clone();
        }
        if self.cardinality_usize() == 0 {
            return other.clone();
        }
        let mut new_data = (*other.data).clone();
        // Overriding self's keys with other's keys if there are some.
        for (k, v) in self.data.iter() {
            if !other.contains(k) {
                new_data.insert(k.clone(), v.clone());
            }
        }
        Self::from_hashmap_owned(new_data)
    }
    pub fn subtract(&self, keys: &Set<K>) -> Self {
        if keys.cardinality_usize() == 0 {
            return self.clone();
        }
        let mut result: HashMap<K, V> = HashMap::new();
        for (k, v) in self.data.iter() {
            if !keys.contains(k) {
                result.insert(k.clone(), v.clone());
            }
        }
        Self::from_hashmap_owned(result)
    }

    pub fn from_hashmap<K2, V2>(
        map: &HashMap<K2, V2>,
        converter_k: fn(&K2) -> K,
        converter_v: fn(&V2) -> V,
    ) -> Map<K, V>
    where
        K: DafnyTypeEq,
        V: DafnyTypeEq,
        K2: Eq + Hash,
        V2: Clone,
    {
        let mut result: HashMap<K, V> = HashMap::new();
        for (k, v) in map.iter() {
            result.insert(converter_k(k), converter_v(v));
        }
        Map {
            data: Rc::new(result),
        }
    }
    pub fn keys(&self) -> Set<K> {
        let mut result: HashSet<K> = HashSet::new();
        for (k, _) in self.data.iter() {
            result.insert(k.clone());
        }
        Set::from_hashset_owned(result)
    }

    pub fn update_index(&self, index: &K, value: &V) -> Self {
        let mut result = self.data.as_ref().clone();
        result.insert(index.clone(), value.clone());
        Map::from_hashmap_owned(result)
    }

    pub fn update_index_owned(&self, index: K, value: V) -> Self {
        let mut result = self.data.as_ref().clone();
        result.insert(index, value);
        Map::from_hashmap_owned(result)
    }

    pub fn iter_raw(&self) -> std::collections::hash_map::Iter<'_, K, V> {
        self.data.iter()
    }

    pub fn iter(&self) -> impl Iterator<Item = K> + '_ {
        self.data.iter().map(|(k, _v)| k).cloned()
    }
}

impl<K: DafnyTypeEq, V: DafnyTypeEq> Map<K, V> {
    pub fn values(&self) -> Set<V> {
        let mut result: Vec<V> = Vec::new();
        for (_, v) in self.data.iter() {
            result.push(v.clone());
        }
        Set::from_array(&result)
    }
    pub fn items(&self) -> Set<(K, V)> {
        let mut result: Vec<(K, V)> = Vec::new();
        for (k, v) in self.data.iter() {
            result.push((k.clone(), v.clone()));
        }
        Set::from_array(&result)
    }
}

impl<K: DafnyTypeEq> Map<K, DafnyInt> {
    pub fn as_dafny_multiset(&self) -> Multiset<K> {
        Multiset::from_hashmap(&self.data)
    }
}

pub struct MapBuilder<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    data: HashMap<K, V>,
}

impl<K, V> Default for MapBuilder<K, V>
where
    K: DafnyTypeEq,
    V: DafnyType,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> MapBuilder<K, V>
where
    K: DafnyTypeEq,
    V: DafnyType,
{
    pub fn new() -> MapBuilder<K, V> {
        MapBuilder {
            data: HashMap::new(),
        }
    }
    pub fn add(&mut self, key: &K, value: &V) {
        // Dafny will prove that overriding has the same value anyway
        self.data.insert(key.clone(), value.clone());
    }
    pub fn build(self) -> Map<K, V> {
        Map::from_hashmap_owned(self.data)
    }
}

impl<K, V> DafnyPrint for Map<K, V>
where
    K: DafnyTypeEq,
    V: DafnyType,
{
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        f.write_str("map[")?;
        let mut first = true;
        for (k, v) in self.data.iter() {
            if !first {
                f.write_str(", ")?;
            }
            first = false;
            k.fmt_print(f, in_seq)?;
            f.write_str(" := ")?;
            v.fmt_print(f, in_seq)?;
        }
        f.write_str("]")
    }
}

impl<K, V> Debug for Map<K, V>
where
    K: DafnyTypeEq,
    V: DafnyTypeEq,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_print(f, false)
    }
}

// **************
// Immutable sets
// **************

#[derive(Clone)]
pub struct Set<V: DafnyTypeEq> {
    data: Rc<HashSet<V>>,
}

// Since there is no canonical way to iterate over a set to compute the hash.
impl<T: DafnyTypeEq> ::std::hash::Hash for Set<T> {
    fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
        self.cardinality_usize().hash(_state)
    }
}

impl<T: DafnyTypeEq> Eq for Set<T> {}

impl<T> Default for Set<T>
where
    T: DafnyTypeEq,
{
    fn default() -> Self {
        Self::new_empty()
    }
}
impl<T: DafnyTypeEq> NontrivialDefault for Set<T> {
    fn nontrivial_default() -> Self {
        Self::default()
    }
}

impl<V> PartialEq<Set<V>> for Set<V>
where
    V: DafnyTypeEq,
{
    fn eq(&self, other: &Set<V>) -> bool {
        // 1. Same cardinality
        // 2. All the elements of self are in the other
        if self.cardinality_usize() != other.cardinality_usize() {
            false
        } else {
            for value in self.data.iter() {
                if !other.contains(value) {
                    return false;
                }
            }
            for value in other.data.iter() {
                if !self.contains(value) {
                    return false;
                }
            }
            true
        }
    }
}

impl<T: DafnyTypeEq> PartialOrd for Set<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // Partial ordering is inclusion
        if self.cardinality_usize() <= other.cardinality_usize() {
            for value in self.data.iter() {
                if !other.contains(value) {
                    return None;
                }
            }
            if self.cardinality_usize() == other.cardinality_usize() {
                Some(Ordering::Equal)
            } else {
                Some(Ordering::Less)
            }
        } else {
            for value in other.data.iter() {
                if !self.contains(value) {
                    return None;
                }
            }
            Some(Ordering::Greater)
        }
    }
}

impl<V: DafnyTypeEq> Set<V> {
    pub fn new_empty() -> Set<V> {
        Self::from_hashset_owned(HashSet::new())
    }
    pub fn from_array(array: &Vec<V>) -> Set<V> {
        Self::from_iterator(array.iter().cloned())
    }
    pub fn from_iterator<I>(data: I) -> Set<V>
    where
        I: Iterator<Item = V>,
    {
        let mut set: HashSet<V> = HashSet::new();
        for value in data {
            set.insert(value);
        }
        Self::from_hashset_owned(set)
    }
    pub fn from_sequence(data: &Rc<Sequence<V>>) -> Set<V> {
        Self::from_array(data.to_array().borrow())
    }
    pub fn from_hashset_owned(hashset: HashSet<V>) -> Set<V> {
        Set {
            data: Rc::new(hashset),
        }
    }
    pub fn cardinality_usize(&self) -> usize {
        self.data.len()
    }
    pub fn cardinality(&self) -> DafnyInt {
        DafnyInt::from_usize(self.data.len())
    }
    pub fn contains(&self, value: &V) -> bool {
        self.data.contains(value)
    }
    pub fn merge(&self, other: &Set<V>) -> Set<V> {
        if self.cardinality_usize() == 0 {
            return other.clone();
        }
        if other.cardinality_usize() == 0 {
            return self.clone();
        }
        let mut result = self.data.as_ref().clone();
        // iterate over the other, add only not contained elements
        for value in other.data.iter() {
            if !result.contains(value) {
                result.insert(value.clone());
            }
        }
        Set::from_hashset_owned(result)
    }

    pub fn intersect(&self, other: &Set<V>) -> Set<V> {
        if self.cardinality_usize() == 0 {
            return self.clone();
        }
        if other.cardinality_usize() == 0 {
            return other.clone();
        }
        // Start with an empty vec with capacity the smallest of both sets
        let mut result = HashSet::new();

        // iterate over the other, take only elements in common
        for value in self.data.iter() {
            if other.data.contains(value) {
                result.insert(value.clone());
            }
        }
        Set::from_hashset_owned(result)
    }

    pub fn subtract(&self, other: &Set<V>) -> Set<V> {
        if self.cardinality_usize() == 0 {
            return self.clone();
        }
        if other.cardinality_usize() == 0 {
            return self.clone();
        }
        // Start with a vec the size of the first one
        let mut result = HashSet::new();

        // iterate over the other, take only elements not in second
        for value in self.data.iter() {
            if !other.contains(value) {
                result.insert(value.clone());
            }
        }
        Set::from_hashset_owned(result)
    }

    pub fn disjoint(&self, other: &Set<V>) -> bool {
        if self.cardinality_usize() == 0 {
            return true;
        }
        if other.cardinality_usize() == 0 {
            return true;
        }
        if other.data.len() < self.data.len() {
            // iterate over the other, take only elements not in self
            for value in other.data.iter() {
                if self.contains(value) {
                    return false;
                }
            }
        } else {
            // iterate over the self, take only elements not in other
            for value in self.data.iter() {
                if other.contains(value) {
                    return false;
                }
            }
        }
        true
    }

    pub fn equals(&self, other: &Set<V>) -> bool {
        if self.cardinality_usize() != other.cardinality_usize() {
            return false;
        }
        // iterate over the other, take only elements not in second
        for value in other.data.iter() {
            if !self.contains(value) {
                return false;
            }
        }
        true
    }

    pub fn elements(&self) -> Set<V> {
        self.clone()
    }

    pub fn as_dafny_multiset(&self) -> Multiset<V> {
        Multiset::from_set(self)
    }

    pub fn iter(&self) -> std::collections::hash_set::Iter<'_, V> {
        self.data.iter()
    }

    pub fn peek(&self) -> V {
        self.data.iter().next().unwrap().clone()
    }
}

pub struct SetBuilder<T>
where
    T: Clone + Eq + Hash,
{
    data: HashMap<T, bool>,
}

impl<T: DafnyTypeEq> Default for SetBuilder<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: DafnyTypeEq> SetBuilder<T> {
    pub fn new() -> SetBuilder<T> {
        SetBuilder {
            data: HashMap::new(),
        }
    }
    pub fn add(&mut self, value: &T) {
        // Dafny will prove that overriding has the same value anyway
        self.data.insert(value.clone(), true);
    }
    pub fn build(self) -> Set<T> {
        // Iterate over all the key values of the hashmap and add them to an array
        let mut result: Vec<T> = Vec::new();
        for (k, _v) in self.data.iter() {
            result.push(k.clone());
        }

        Set::from_array(&result)
    }
}

impl<V: DafnyTypeEq> DafnyPrint for Set<V> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        f.write_str("{")?;
        let mut first = true;
        for value in self.data.iter() {
            if !first {
                f.write_str(", ")?;
            }
            first = false;
            value.fmt_print(f, in_seq)?;
        }
        f.write_str("}")
    }
}

impl<V> Debug for Set<V>
where
    V: DafnyTypeEq,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_print(f, false)
    }
}

// *******************
// Immutable multisets
// *******************

#[derive(Clone)]
pub struct Multiset<V: DafnyTypeEq> {
    pub data: HashMap<V, DafnyInt>,
    pub size: DafnyInt,
}

impl<V: DafnyTypeEq> Multiset<V> {
    pub fn new_empty() -> Multiset<V> {
        Self::from_array(&vec![])
    }
    pub fn get_total(map: &HashMap<V, DafnyInt>) -> DafnyInt {
        let mut total = DafnyInt::zero();
        for (_, v) in map.iter() {
            total = total + v.clone();
        }
        total
    }
    pub fn from_hashmap_owned(map: HashMap<V, DafnyInt>) -> Multiset<V> {
        Multiset {
            size: Self::get_total(&map),
            data: map,
        }
    }
    pub fn from_hashmap(map: &HashMap<V, DafnyInt>) -> Multiset<V> {
        Self::from_hashmap_owned(map.clone())
    }
    pub fn from_array(data: &Vec<V>) -> Multiset<V> {
        Self::from_iterator(data.iter().cloned())
    }
    pub fn from_iterator<I>(data: I) -> Multiset<V>
    where
        I: Iterator<Item = V>,
    {
        let mut hashmap: HashMap<V, DafnyInt> = HashMap::new();
        let mut total: DafnyInt = DafnyInt::zero();
        for value in data {
            let count = hashmap.entry(value.clone()).or_insert(DafnyInt::zero());
            *count = count.clone() + DafnyInt::one();
            total = total + DafnyInt::one();
        }
        Multiset {
            data: hashmap,
            size: total,
        }
    }
    pub fn from_set(set: &Set<V>) -> Multiset<V> {
        Self::from_iterator(set.data.iter().cloned())
    }

    pub fn cardinality_usize(&self) -> SizeT {
        self.size.as_usize()
    }
    pub fn cardinality(&self) -> DafnyInt {
        self.size.clone()
    }
    pub fn contains(&self, value: &V) -> bool {
        self.data.contains_key(value) && self.data.get(value).unwrap() > &DafnyInt::zero()
    }
    pub fn get(&self, value: &V) -> DafnyInt {
        if self.data.contains_key(value) {
            self.data.get(value).unwrap().clone()
        } else {
            DafnyInt::zero()
        }
    }
    pub fn update_count(&self, value: &V, new_count: &DafnyInt) -> Multiset<V> {
        let mut result = self.clone();
        let old_count = self.get(value);
        if new_count == &DafnyInt::zero() {
            result.data.remove(value);
        } else {
            result.data.insert(value.clone(), new_count.clone());
        }
        result.size = self.size.clone() + new_count.clone() - old_count;
        result
    }
    pub fn merge(&self, other: &Multiset<V>) -> Multiset<V> {
        if other.size.is_zero() {
            return self.clone();
        }
        if self.size.is_zero() {
            return other.clone();
        }
        let mut result = self.data.clone();
        for (k, v) in other.data.iter() {
            let old_count = self.get(k);
            let new_count = old_count.clone() + v.clone();
            result.insert(k.clone(), new_count);
        }
        Multiset {
            data: result,
            size: self.size.clone() + other.size.clone(),
        }
    }
    pub fn intersect(&self, other: &Multiset<V>) -> Multiset<V> {
        if other.size.is_zero() {
            return other.clone();
        }
        if self.size.is_zero() {
            return self.clone();
        }
        let mut result = HashMap::<V, DafnyInt>::new();
        let mut total = DafnyInt::zero();
        for (k, other_count) in other.data.iter() {
            let self_count = self.get(k);
            let resulting_count = if self_count < *other_count {
                self_count
            } else {
                other_count.clone()
            };
            if resulting_count.is_positive() {
                result.insert(k.clone(), resulting_count.clone());
                total = total + resulting_count;
            }
        }
        Multiset {
            data: result,
            size: total,
        }
    }
    pub fn subtract(&self, other: &Multiset<V>) -> Multiset<V> {
        if other.size.is_zero() {
            return self.clone();
        }
        if self.size.is_zero() {
            return self.clone();
        }
        let mut result = self.data.clone();
        let mut total = self.size.clone();
        for (k, v) in other.data.iter() {
            let old_count = self.get(k);
            let new_count = old_count.clone() - v.clone();
            if !new_count.is_positive() {
                total = total - old_count.clone();
                result.remove(k);
            } else {
                total = total - v.clone();
                result.insert(k.clone(), new_count);
            }
        }
        Multiset {
            data: result,
            size: total,
        }
    }
    pub fn disjoint(&self, other: &Multiset<V>) -> bool {
        for value in other.data.keys() {
            if self.contains(value) {
                return false;
            }
        }
        true
    }

    pub fn as_dafny_multiset(&self) -> Multiset<V> {
        self.clone()
    }

    pub fn peek(&self) -> V {
        self.data.iter().next().unwrap().0.clone()
    }

    pub fn iter_raw(&self) -> std::collections::hash_map::Iter<'_, V, DafnyInt> {
        self.data.iter()
    }

    pub fn iter(&self) -> impl Iterator<Item = V> + '_ {
        self.data
            .iter()
            .flat_map(|(k, v)| ::std::iter::repeat(k).take(v.clone().as_usize()))
            .cloned()
    }
}

impl<T> Default for Multiset<T>
where
    T: DafnyTypeEq,
{
    fn default() -> Self {
        Self::new_empty()
    }
}
impl<T: DafnyTypeEq> NontrivialDefault for Multiset<T> {
    fn nontrivial_default() -> Self {
        Self::default()
    }
}

impl<V: DafnyTypeEq> PartialOrd<Multiset<V>> for Multiset<V> {
    fn partial_cmp(&self, other: &Multiset<V>) -> Option<Ordering> {
        match self.cardinality().cmp(&other.cardinality()) {
            Ordering::Less => {
                for value in self.data.keys() {
                    if !other.contains(value) || self.get(value) > other.get(value) {
                        return None;
                    }
                }
                Some(Ordering::Less)
            }
            Ordering::Equal => {
                for value in self.data.keys() {
                    if self.get(value) != other.get(value) {
                        return None;
                    }
                }
                Some(Ordering::Equal)
            }
            Ordering::Greater => {
                for value in other.data.keys() {
                    if !self.contains(value) || self.get(value) < other.get(value) {
                        return None;
                    }
                }
                Some(Ordering::Greater)
            }
        }
    }
}

impl<V: DafnyTypeEq> DafnyPrint for Multiset<V> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        f.write_str("multiset{")?;
        let mut first = true;
        for value in self.data.iter() {
            for _count in 0..value.1.as_usize() {
                if !first {
                    f.write_str(", ")?;
                }
                first = false;
                value.0.fmt_print(f, in_seq)?;
            }
        }
        f.write_str("}")
    }
}

impl<V> Debug for Multiset<V>
where
    V: DafnyTypeEq,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_print(f, false)
    }
}

impl<V: DafnyTypeEq> PartialEq<Multiset<V>> for Multiset<V> {
    fn eq(&self, other: &Multiset<V>) -> bool {
        if self.cardinality() != other.cardinality() {
            return false;
        }
        // iterate over the other, take only elements not in second
        for value in other.data.iter() {
            if !self.contains(value.0) || self.get(value.0) != *value.1 {
                return false;
            }
        }
        true
    }
}
impl<V: DafnyTypeEq> Eq for Multiset<V> {}
impl<V: DafnyTypeEq> Hash for Multiset<V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.cardinality().hash(state);
    }
}

pub fn euclidian_division<A: Signed + Zero + One + Clone + PartialEq>(a: A, b: A) -> A {
    if !a.is_negative() {
        if !b.is_negative() {
            a / b
        } else {
            -(a / -b)
        }
    } else {
        if !b.is_negative() {
            -((-(a + One::one())) / b) - One::one()
        } else {
            (-(a + One::one())) / (-b) + One::one()
        }
    }
}

pub fn euclidian_modulo<A: Signed + Zero + One + Clone + PartialEq>(a: A, b: A) -> A {
    if !a.is_negative() {
        if !b.is_negative() {
            a % b
        } else {
            a % -b
        }
    } else {
        let bp = b.abs();
        let c = (-a) % bp.clone();
        if c == Zero::zero() {
            Zero::zero()
        } else {
            bp - c
        }
    }
}

pub struct IntegerRange<A: Add<Output = A> + One + Ord + Clone> {
    hi: A,
    current: A,
}

impl<A: Add<Output = A> + One + Ord + Clone> Iterator for IntegerRange<A> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.hi {
            let result = self.current.clone();
            self.current = self.current.clone() + One::one();
            Some(result)
        } else {
            None
        }
    }
}

pub fn integer_range<A: Add<Output = A> + One + Ord + Clone>(
    low: A,
    hi: A,
) -> impl Iterator<Item = A> {
    IntegerRange { hi, current: low }
}

pub struct IntegerRangeDown<A: Sub<Output = A> + One + Ord + Clone> {
    current: A,
    low: A,
}

impl<A: Sub<Output = A> + One + Ord + Clone> Iterator for IntegerRangeDown<A> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current > self.low {
            self.current = self.current.clone() - One::one();
            Some(self.current.clone())
        } else {
            None
        }
    }
}

pub fn integer_range_down<A: Sub<Output = A> + One + Ord + Clone>(
    hi: A,
    low: A,
) -> impl Iterator<Item = A> {
    IntegerRangeDown { current: hi, low }
}

// Unbounded versions

pub struct IntegerRangeUnbounded<A: Add<Output = A> + One + Clone> {
    current: A,
}
impl<A: Add<Output = A> + One + Clone> Iterator for IntegerRangeUnbounded<A> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        let result = self.current.clone();
        self.current = self.current.clone() + One::one();
        Some(result)
    }
}
pub fn integer_range_unbounded<A: Add<Output = A> + One + Clone>(
    low: A,
) -> impl Iterator<Item = A> {
    IntegerRangeUnbounded { current: low }
}

pub struct IntegerRangeDownUnbounded<A: Sub<Output = A> + One + Clone> {
    current: A,
}

impl<A: Sub<Output = A> + One + Clone> Iterator for IntegerRangeDownUnbounded<A> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.current = self.current.clone() - One::one();
        Some(self.current.clone())
    }
}

pub fn integer_range_down_unbounded<A: Sub<Output = A> + One + Clone>(
    hi: A,
) -> impl Iterator<Item = A> {
    IntegerRangeDownUnbounded { current: hi }
}

pub struct LazyFieldWrapper<A>(pub Lazy<A, Box<dyn 'static + FnOnce() -> A>>);

impl<A: PartialEq> PartialEq for LazyFieldWrapper<A> {
    fn eq(&self, other: &Self) -> bool {
        self.0.deref() == other.0.deref()
    }
}

impl<A: Default + 'static> Default for LazyFieldWrapper<A> {
    fn default() -> Self {
        Self(Lazy::new(Box::new(A::default)))
    }
}

impl<A: DafnyPrint> DafnyPrint for LazyFieldWrapper<A> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        self.0.deref().fmt_print(f, in_seq)
    }
}

#[cfg(feature = "sync")]
// Convert the DafnyPrint above into a macro so that we can create it for functions of any input arity
macro_rules! dafny_print_function {
    ($($n:tt)*) => {
        impl <B, $($n),*> $crate::DafnyPrint for $crate::Rc<dyn ::std::ops::Fn($(&$n),*) -> B + Send + Sync> {
            fn fmt_print(&self, f: &mut ::std::fmt::Formatter<'_>, _in_seq: bool) -> ::std::fmt::Result {
                write!(f, "<function>")
            }
        }
    }
}
#[cfg(not(feature = "sync"))]
// Convert the DafnyPrint above into a macro so that we can create it for functions of any input arity
macro_rules! dafny_print_function {
    ($($n:tt)*) => {
        impl <B, $($n),*> $crate::DafnyPrint for $crate::Rc<dyn ::std::ops::Fn($(&$n),*) -> B> {
            fn fmt_print(&self, f: &mut ::std::fmt::Formatter<'_>, _in_seq: bool) -> ::std::fmt::Result {
                write!(f, "<function>")
            }
        }
    }
}

// Now create a loop like impl_tuple_print_loop so that we can create functions up to size 32
macro_rules! dafny_print_function_loop {
    ($first:ident $($rest:ident)*) => {
        dafny_print_function_loop! { $($rest)* }
        dafny_print_function! { $first $($rest)* }
    };
    () => {
    }
}
// Emit functions till 32 parameters
dafny_print_function_loop! { A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16
A17 A18 A19 A20 A21 A22 A23 A24 A25 A26 A27 A28 A29 A30 A31 A32 }

pub struct FunctionWrapper<A: ?Sized>(pub A);
impl<A> DafnyPrint for FunctionWrapper<A> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "<function>")
    }
}

impl<A: Clone> Clone for FunctionWrapper<A> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<A: ?Sized> PartialEq for FunctionWrapper<Rc<A>> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

pub struct DafnyPrintWrapper<T>(pub T);
impl<T: DafnyPrint> Display for DafnyPrintWrapper<&T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_print(f, false)
    }
}

pub trait DafnyPrint {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result;

    // Vec<char> gets special treatment so we carry that information here
    #[inline]
    fn is_char() -> bool {
        false
    }
}

impl<T> DafnyPrint for *const T {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "<{} object>", std::any::type_name::<T>())
    }
}

macro_rules! impl_print_display {
    ($name:ty) => {
        impl $crate::DafnyPrint for $name {
            fn fmt_print(
                &self,
                f: &mut ::std::fmt::Formatter<'_>,
                _in_seq: bool,
            ) -> ::std::fmt::Result {
                ::std::fmt::Display::fmt(&self, f)
            }
        }
    };
}

impl_print_display! { String }
impl_print_display! { bool }
impl_print_display! { u8 }
impl_print_display! { u16 }
impl_print_display! { u32 }
impl_print_display! { u64 }
impl_print_display! { u128 }
impl_print_display! { i8 }
impl_print_display! { i16 }
impl_print_display! { i32 }
impl_print_display! { i64 }
impl_print_display! { i128 }
impl_print_display! { usize }

impl DafnyPrint for f32 {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{:.1}", self)
    }
}

impl DafnyPrint for f64 {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{:.1}", self)
    }
}

impl DafnyPrint for () {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "()")
    }
}

#[derive(Clone, Copy)]
pub struct DafnyCharUTF16(pub u16);
pub type DafnyStringUTF16 = Sequence<DafnyCharUTF16>;

impl Default for DafnyCharUTF16 {
    fn default() -> Self {
        Self('a' as u16)
    }
}

impl DafnyPrint for DafnyCharUTF16 {
    #[inline]
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        let real_char = char::decode_utf16([*self].iter().map(|v| v.0))
            .map(|r| r.map_err(|e| e.unpaired_surrogate()))
            .collect::<Vec<_>>()[0];
        let rendered_char = match real_char {
            Ok(c) => c,
            Err(e) => {
                return write!(f, "Invalid UTF-16 code point: {}", e);
            }
        };

        if in_seq {
            write!(f, "{}", rendered_char)
        } else {
            write!(f, "'{}'", rendered_char)
        }
    }

    #[inline]
    fn is_char() -> bool {
        true
    }
}

impl Debug for DafnyCharUTF16 {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_print(f, false)
    }
}

impl PartialEq<DafnyCharUTF16> for DafnyCharUTF16 {
    fn eq(&self, other: &DafnyCharUTF16) -> bool {
        self.0 == other.0
    }
}
impl Eq for DafnyCharUTF16 {}
impl Hash for DafnyCharUTF16 {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl PartialOrd<DafnyCharUTF16> for DafnyCharUTF16 {
    fn partial_cmp(&self, other: &DafnyCharUTF16) -> Option<Ordering> {
        (self.0).partial_cmp(&other.0)
    }
}

impl Add<DafnyCharUTF16> for DafnyCharUTF16 {
    type Output = DafnyCharUTF16;

    fn add(self, rhs: DafnyCharUTF16) -> Self::Output {
        DafnyCharUTF16(self.0 + rhs.0)
    }
}

impl Sub<DafnyCharUTF16> for DafnyCharUTF16 {
    type Output = DafnyCharUTF16;

    fn sub(self, rhs: DafnyCharUTF16) -> Self::Output {
        DafnyCharUTF16(self.0 - rhs.0)
    }
}

#[derive(Clone, Copy)]
pub struct DafnyChar(pub char);
pub type DafnyString = Sequence<DafnyChar>;

impl Default for DafnyChar {
    fn default() -> Self {
        Self('a')
    }
}

impl DafnyPrint for DafnyChar {
    #[inline]
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        if in_seq {
            write!(f, "{}", self.0)
        } else {
            write!(f, "'{}'", self.0)
        }
    }

    #[inline]
    fn is_char() -> bool {
        true
    }
}

impl Debug for DafnyChar {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_print(f, false)
    }
}

impl PartialEq<DafnyChar> for DafnyChar {
    fn eq(&self, other: &DafnyChar) -> bool {
        self.0 == other.0
    }
}

impl PartialOrd<DafnyChar> for DafnyChar {
    fn partial_cmp(&self, other: &DafnyChar) -> Option<Ordering> {
        (self.0 as u32).partial_cmp(&(other.0 as u32))
    }
}
impl Eq for DafnyChar {}
impl Hash for DafnyChar {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.hash(state)
    }
}

impl Add<DafnyChar> for DafnyChar {
    type Output = DafnyChar;

    fn add(self, rhs: DafnyChar) -> Self::Output {
        DafnyChar(unsafe { char::from_u32_unchecked(self.0 as u32 + rhs.0 as u32) })
    }
}

impl Sub<DafnyChar> for DafnyChar {
    type Output = DafnyChar;

    fn sub(self, rhs: DafnyChar) -> Self::Output {
        DafnyChar(unsafe { char::from_u32_unchecked(self.0 as u32 - rhs.0 as u32) })
    }
}

impl<T: DafnyPrint> DafnyPrint for Option<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        match self {
            Some(x) => x.fmt_print(f, false),
            None => write!(f, "null"),
        }
    }
}

impl<T: ?Sized + DafnyPrint> DafnyPrint for Rc<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        self.as_ref().fmt_print(f, in_seq)
    }
}

impl<T: ?Sized + DafnyPrint> DafnyPrint for &Rc<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        self.as_ref().fmt_print(f, in_seq)
    }
}

impl<T: DafnyPrint> DafnyPrint for Vec<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        if !T::is_char() {
            write!(f, "[")?;
        }

        for (i, item) in self.iter().enumerate() {
            if !T::is_char() {
                if i > 0 {
                    write!(f, ", ")?;
                }

                item.fmt_print(f, false)?;
            } else {
                item.fmt_print(f, true)?;
            }
        }

        if !T::is_char() {
            write!(f, "]")
        } else {
            Ok(())
        }
    }
}

#[cfg(not(feature = "sync"))]
impl<T: DafnyPrint> DafnyPrint for RefCell<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        self.borrow().fmt_print(f, _in_seq)
    }
}

#[cfg(feature = "sync")]
impl<T: DafnyPrint> DafnyPrint for RefCell<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        self.lock().unwrap().fmt_print(f, _in_seq)
    }
}

impl<T: DafnyPrint> DafnyPrint for HashSet<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{{")?;

        for (i, item) in self.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            item.fmt_print(f, false)?;
        }

        write!(f, "}}")
    }
}

pub fn char_lt(left: char, right: char) -> bool {
    let left_code = left as u32;
    let right_code = right as u32;

    left_code < right_code
}

pub fn string_of(s: &str) -> DafnyString {
    s.chars().map(DafnyChar).collect::<Sequence<DafnyChar>>()
}

pub fn string_utf16_of(s: &str) -> DafnyStringUTF16 {
    Sequence::from_array_owned(s.encode_utf16().map(DafnyCharUTF16).collect())
}

macro_rules! impl_tuple_print {
    ($($items:ident)*) => {
        impl <$($items,)*> $crate::DafnyPrint for ($($items,)*)
        where
            $($items: $crate::DafnyPrint,)*
        {
            #[allow(unused_assignments)]
            fn fmt_print(&self, f: &mut ::std::fmt::Formatter<'_>, _in_seq: bool) -> ::std::fmt::Result {
                #[allow(non_snake_case)]
                let ($($items,)*) = self;

                write!(f, "(")?;

                let mut i = 0;

                $(
                    if (i > 0) {
                        write!(f, ", ")?;
                    }

                    $items.fmt_print(f, false)?;

                    i += 1;
                )*

                write!(f, ")")
            }
        }
    };
}

macro_rules! impl_tuple_print_loop {
    () => {};
    ($first:ident $($rest:ident)*) => {
        impl_tuple_print_loop! { $($rest)* }
        impl_tuple_print! { $first $($rest)* }
    };
}

// 32 elements ought to be enough for everyone
impl_tuple_print_loop! {
    A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10
    A11 A12 A13 A14 A15 A16 A17 A18 A19 A20
    A21 A22 A23 A24 A25 A26 A27 A28 A29 A30
    A31
}

// seq!(1, 2, 3) is rewritten to Sequence::from_array_owned(vec!(1, 2, 3))
#[macro_export]
macro_rules! seq {
    ($($x:expr),*) => {
        $crate::Sequence::from_array_owned(vec![$($x), *])
    }
}

#[macro_export]
macro_rules! set {
    ($($x:expr), *) => {
        {
            // No warning about this variable not needing to be mut in the case of an empty set
            #[allow(unused_mut)]
            let mut temp_hash = ::std::collections::HashSet::new();
            $(
                temp_hash.insert($x);
            )*
            $crate::Set::from_hashset_owned(temp_hash)
        }
    }
}

#[macro_export]
macro_rules! multiset {
    ($($x:expr), *) => {
        {
            #[allow(unused_mut)]
            let mut temp_hash = ::std::collections::HashMap::new();
            #[allow(unused_mut)]
            let mut total_size: usize = 0;
            $( {
                #[allow(unused_mut)]
                let mut entry = temp_hash.entry($x).or_insert($crate::DafnyInt::from(0));
                *entry = (*entry).clone() + $crate::DafnyInt::from(1);
                total_size += 1;
              }
            )*
            $crate::Multiset {
                data: temp_hash,
                size: $crate::DafnyInt::from(total_size),
            }
        }
    }
}

// we enable the syntax map![k1 => v1, k2 => v2]
#[macro_export]
macro_rules! map {
    ($($k:expr => $v:expr), *) => {
        {
            #[allow(unused_mut)]
            let mut temp_hash = ::std::collections::HashMap::new();
            $(
                temp_hash.insert($k.clone(), $v.clone());
            )*
            $crate::Map::from_hashmap_owned(temp_hash)
        }
    }
}

#[macro_export]
macro_rules! int {
    ($x:expr) => {
        $crate::DafnyInt::from($x)
    };
}

//////////
// Arrays
//////////

macro_rules! ARRAY_GETTER_LENGTH0 {
    () => {
        #[inline]
        pub fn length0(&self) -> $crate::DafnyInt {
            $crate::DafnyInt::from(self.length0_usize())
        }
        #[inline]
        pub fn length0_usize(&self) -> usize {
            self.data.len()
        }
    };
}
macro_rules! ARRAY_GETTER_LENGTH {
    ($field: ident, $field_usize: ident) => {
        #[inline]
        pub fn $field(&self) -> $crate::DafnyInt {
            $crate::DafnyInt::from(self.$field_usize())
        }
        #[inline]
        pub fn $field_usize(&self) -> usize {
            self.$field
        }
    };
}

// An 1-dimensional Dafny array is a zero-cost abstraction over a pointer on a native array
#[macro_export]
macro_rules! array {
    ($($x:expr), *) => {
        $crate::array::from_native(::std::boxed::Box::new([$($x), *]))
    }
}

macro_rules! ARRAY_INIT {
    {$length: ident, $inner: expr} => {
        $crate::array::initialize_box_usize($length, {
            $crate::Rc::new(move |_| { $inner })
        })
    }
}

macro_rules! ARRAY_INIT_INNER {
    ($length: ident) => {
        $crate::array::placebos_box_usize::<T>($length)
    };
}

// ARRAY_DATA_TYPE(length0, length1, length2) will return
// Box<[Box<[Box<[T]>]>]>
macro_rules! ARRAY_DATA_TYPE {
    ($length:ident) => {
        ::std::boxed::Box<[T]>
    };
    ($length:ident, $($rest_length:ident),+) => {
        ::std::boxed::Box<[ARRAY_DATA_TYPE!($($rest_length),+)]>
    };
}

// Macro to generate generalizations of the function placebos_usize to higher-dimensions arrays

#[macro_export]
macro_rules! INIT_ARRAY_DATA {
    // Handle the innermost array initialization
    ($ArrayType:ident, $last_length:ident) => {
        ARRAY_INIT_INNER!($last_length)
    };
    // Handle recursive array initialization for multiple dimensions
    ($ArrayType:ident, $first_length:ident, $($rest_length:ident),+) => {
        ARRAY_INIT!($first_length, INIT_ARRAY_DATA!($ArrayType, $($rest_length),+))
    };
}

macro_rules! ARRAY_METHODS {
    // Accepts any number of length identifiers
    ($ArrayType:ident, $length0: ident, $($length:ident),+) => {
        pub fn placebos_box_usize(
            $length0: usize,
            $($length: usize),+
        ) -> ::std::boxed::Box<$ArrayType<$crate::MaybeUninit<T>>> {
            ::std::boxed::Box::new($ArrayType {
                $($length: $length),+,
                data: INIT_ARRAY_DATA!($ArrayType, $length0, $($length),+),
            })
        }

        pub fn placebos_usize(
            $length0: usize,
            $($length: usize),+
        ) -> $crate::Ptr<$ArrayType<$crate::MaybeUninit<T>>> {
            $crate::Ptr::from_box(Self::placebos_box_usize(
                $length0,
                $($length),+
            ))
        }

        pub fn placebos_usize_object(
            $length0: usize,
            $($length: usize),+
        ) -> $crate::Object<$ArrayType<$crate::MaybeUninit<T>>> {
            // SAFETY: We know the object is owned and never referred to by anything else
            $crate::Object::new($ArrayType {
                $($length: $length),+,
                data: INIT_ARRAY_DATA!($ArrayType, $length0, $($length),+),
            })
        }

        pub fn placebos(
            $length0: &$crate::DafnyInt,
            $($length: &$crate::DafnyInt),+
        ) -> $crate::Ptr<$ArrayType<$crate::MaybeUninit<T>>> {
            Self::placebos_usize(
                $length0.as_usize(),
                $($length.as_usize()),+
            )
        }

        // Once all the elements have been initialized, transform the signature of the pointer
        pub fn construct(p: $crate::Ptr<$ArrayType<$crate::MaybeUninit<T>>>) -> $crate::Ptr<$ArrayType<T>> {
            unsafe { std::mem::transmute(p) }
        }
        // Once all the elements have been initialized, transform the signature of the pointer
        pub fn construct_object(p: $crate::Object<$ArrayType<$crate::MaybeUninit<T>>>) -> $crate::Object<$ArrayType<T>> {
            unsafe { std::mem::transmute(p) }
        }
    };
}

macro_rules! ARRAY_STRUCT {
    ($ArrayType:ident, $length0: ident, $($length:ident),+) => {
        pub struct $ArrayType<T> {
            $($length: usize),+,
            pub data: ARRAY_DATA_TYPE!($length0, $($length),+),
        }
    }
}

macro_rules! ARRAY_TO_VEC_LOOP {
    (@inner $self: ident, $tmp: ident, $data: expr) => {
        $tmp.push($data.clone());
    };
    (@for $self: ident, $tmp: ident, $data: expr, $length_usize: ident $(, $rest_length_usize: ident)*) => {
        for i in 0..$self.$length_usize() {
            ARRAY_TO_VEC_LOOP!(@inner $self, $tmp, $data[i] $(, $rest_length_usize)*);
        }
    };
    (@inner $self: ident, $outerTmp: ident, $data: expr $(, $rest_length_usize: ident)*) => {
        {
            let mut tmp = ::std::vec::Vec::new();
            ARRAY_TO_VEC_LOOP!(@for $self, tmp, $data $(, $rest_length_usize)*);
            $outerTmp.push(tmp);
        }
    };

    ($self: ident, $data: expr $(, $rest_length_usize: ident)*) => {
        {
            let mut tmp = ::std::vec::Vec::new();
            ARRAY_TO_VEC_LOOP!(@for $self, tmp, $data $(, $rest_length_usize)*);
            tmp
        }
    };
}

macro_rules! ARRAY_TO_VEC_TYPE {
    ($length0: ident) => {
        ::std::vec::Vec<T>
    };
    ($length0: ident $(, $res_length: ident)*) => {
        ::std::vec::Vec<ARRAY_TO_VEC_TYPE!($($res_length), *)>
    }
}

macro_rules! ARRAY_TO_VEC {
    ($length0_usize: ident $(, $res_length_usize: ident)*) => {
        pub fn to_vec(&self) -> ARRAY_TO_VEC_TYPE!($length0_usize, $($res_length_usize),*) {
            ARRAY_TO_VEC_LOOP!(self, self.data, $length0_usize, $($res_length_usize),*)
        }
    }
}

macro_rules! ARRAY_LENGTHS {
    () => {

    };
    (($length0: ident, $length0_usize: ident) $(, $rest: tt)*) => {
        ARRAY_GETTER_LENGTH0!();
        ARRAY_LENGTHS!($(, $rest)*);
    };
    (, ($length: ident, $length_usize: ident) $(, $rest: tt)*) => {
        ARRAY_GETTER_LENGTH!($length, $length_usize);
        ARRAY_LENGTHS!($(, $rest)*);
    }
}

macro_rules! ARRAY_METHODS_WRAPPER {
    ($ArrayType:ident, $(($length:ident, $length_usize: ident)), +) => {
        ARRAY_METHODS!($ArrayType, $($length), +);
    }
}

macro_rules! ARRAY_TO_VEC_WRAPPER {
    ($(($length:ident, $length_usize: ident)), +) => {
        ARRAY_TO_VEC!($($length_usize), +);
    }
}

macro_rules! ARRAY_STRUCT_WRAPPER {
    ($ArrayType:ident, $(($length:ident, $length_usize: ident)), +) => {
        ARRAY_STRUCT!($ArrayType, $($length), +);
    }
}

macro_rules! ARRAY_DEF {
    ($ArrayType:ident, $(($length:ident, $length_usize: ident)), +) => {
        ARRAY_STRUCT_WRAPPER!($ArrayType, $(($length, $length_usize)), +);
        impl<T> $ArrayType<T> {
            ARRAY_LENGTHS!{
                $(($length, $length_usize)), +
            }
            ARRAY_METHODS_WRAPPER!{$ArrayType,
                $(($length, $length_usize)), +
            }
        }
        impl<T: ::std::clone::Clone> $ArrayType<T> {
            ARRAY_TO_VEC_WRAPPER!{
                $(($length, $length_usize)), +
            }
        }
    }
}

// Array2 to Array16

ARRAY_DEF! {Array2,
    (length0, length0_usize),
    (length1, length1_usize)
}

ARRAY_DEF! {Array3,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize)
}

ARRAY_DEF! {Array4,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize)
}

ARRAY_DEF! {Array5,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize)
}

ARRAY_DEF! {Array6,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize)
}

ARRAY_DEF! {Array7,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize)
}

ARRAY_DEF! {Array8,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize)
}

ARRAY_DEF! {Array9,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize),
    (length8, length8_usize)
}

ARRAY_DEF! {Array10,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize),
    (length8, length8_usize),
    (length9, length9_usize)
}

ARRAY_DEF! {Array11,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize),
    (length8, length8_usize),
    (length9, length9_usize),
    (length10, length10_usize)
}

ARRAY_DEF! {Array12,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize),
    (length8, length8_usize),
    (length9, length9_usize),
    (length10, length10_usize),
    (length11, length11_usize)
}

ARRAY_DEF! {Array13,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize),
    (length8, length8_usize),
    (length9, length9_usize),
    (length10, length10_usize),
    (length11, length11_usize),
    (length12, length12_usize)
}

ARRAY_DEF! {Array14,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize),
    (length8, length8_usize),
    (length9, length9_usize),
    (length10, length10_usize),
    (length11, length11_usize),
    (length12, length12_usize),
    (length13, length13_usize)
}

ARRAY_DEF! {Array15,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize),
    (length8, length8_usize),
    (length9, length9_usize),
    (length10, length10_usize),
    (length11, length11_usize),
    (length12, length12_usize),
    (length13, length13_usize),
    (length14, length14_usize)
}

ARRAY_DEF! {Array16,
    (length0, length0_usize),
    (length1, length1_usize),
    (length2, length2_usize),
    (length3, length3_usize),
    (length4, length4_usize),
    (length5, length5_usize),
    (length6, length6_usize),
    (length7, length7_usize),
    (length8, length8_usize),
    (length9, length9_usize),
    (length10, length10_usize),
    (length11, length11_usize),
    (length12, length12_usize),
    (length13, length13_usize),
    (length14, length14_usize),
    (length15, length15_usize)
}

pub mod array {
    use super::DafnyInt;
    use super::Ptr;
    use super::Rc;
    use ::std::boxed::Box;
    use ::std::mem::MaybeUninit;
    use ::std::vec::Vec;
    use num::ToPrimitive;

    #[inline]
    pub fn from_native<T>(v: Box<[T]>) -> Ptr<[T]> {
        Ptr::from_box(v)
    }
    #[inline]
    pub fn from_vec<T>(v: Vec<T>) -> Ptr<[T]> {
        from_native(v.into_boxed_slice())
    }
    pub fn to_vec<T>(v: Ptr<[T]>) -> Vec<T> {
        unsafe { Box::<[T]>::from_raw(v.into_raw()) }.into_vec()
    }
    pub fn initialize_usize<T>(n: usize, initializer: Rc<dyn Fn(usize) -> T>) -> Ptr<[T]> {
        let mut v = Vec::with_capacity(n);
        for i in 0..n {
            v.push(initializer(i));
        }
        from_vec(v)
    }

    pub fn placebos<T>(n: &DafnyInt) -> Ptr<[MaybeUninit<T>]> {
        placebos_usize(n.as_usize())
    }
    pub fn placebos_usize<T>(n: usize) -> Ptr<[MaybeUninit<T>]> {
        Ptr::from_box(placebos_box_usize(n))
    }
    pub fn placebos_usize_object<T>(n: usize) -> super::Object<[MaybeUninit<T>]> {
        super::rcmut::array_object_from_box(placebos_box_usize(n))
    }
    // Once all the elements have been initialized, transform the signature of the pointer
    pub fn construct<T>(p: Ptr<[MaybeUninit<T>]>) -> Ptr<[T]> {
        unsafe { std::mem::transmute(p) }
    }
    pub fn construct_object<T>(p: super::Object<[MaybeUninit<T>]>) -> super::Object<[T]> {
        unsafe { std::mem::transmute(p) }
    }

    pub fn placebos_box<T>(n: &DafnyInt) -> Box<[MaybeUninit<T>]> {
        placebos_box_usize(n.to_usize().unwrap())
    }
    pub fn placebos_box_usize<T>(n_usize: usize) -> Box<[MaybeUninit<T>]> {
        // This code is optimized to take a constant time. See:
        // https://users.rust-lang.org/t/allocate-a-boxed-array-of-maybeuninit/110169/7
        std::iter::repeat_with(MaybeUninit::uninit)
            .take(n_usize)
            .collect()
    }

    pub fn initialize<T>(n: &DafnyInt, initializer: Rc<dyn Fn(&DafnyInt) -> T>) -> Ptr<[T]> {
        Ptr::from_box(initialize_box(n, initializer))
    }

    pub fn initialize_box<T>(n: &DafnyInt, initializer: Rc<dyn Fn(&DafnyInt) -> T>) -> Box<[T]> {
        initialize_box_usize(n.to_usize().unwrap(), initializer)
    }
    pub fn initialize_box_usize<T>(
        n_usize: usize,
        initializer: Rc<dyn Fn(&DafnyInt) -> T>,
    ) -> Box<[T]> {
        let mut v = Vec::with_capacity(n_usize);
        for i in 0..n_usize {
            v.push(initializer(&int!(i)));
        }
        v.into_boxed_slice()
    }

    #[inline]
    pub fn length_usize<T>(this: Ptr<[T]>) -> usize {
        // safety: Dafny won't call this function unless it can guarantee the array is still allocated
        super::read!(this).len()
    }
    #[inline]
    pub fn length<T>(this: Ptr<[T]>) -> DafnyInt {
        int!(length_usize(this))
    }
    #[inline]
    pub fn get_usize<T: Clone>(this: Ptr<[T]>, i: usize) -> T {
        // safety: Dafny won't call this function unless it can guarantee the array is still allocated
        this.as_ref()[i].clone()
    }
    #[inline]
    pub fn get<T: Clone>(this: Ptr<[T]>, i: &DafnyInt) -> T {
        get_usize(this, i.to_usize().unwrap())
    }
    #[inline]
    pub fn update_usize<T>(this: Ptr<[T]>, i: usize, val: T) {
        // safety: Dafny won't call this function unless it can guarantee the array is still allocated
        crate::modify!(this)[i] = val;
    }
    #[inline]
    pub fn update<T>(this: Ptr<[T]>, i: &DafnyInt, val: T) {
        update_usize(this, i.to_usize().unwrap(), val);
    }
}

///////////////////
// Class helpers //
///////////////////
pub fn allocate<T>() -> Ptr<T> {
    let this_ptr = Box::into_raw(Box::new(MaybeUninit::uninit())) as *mut MaybeUninit<T> as *mut T;
    Ptr::from_raw_nonnull(this_ptr)
}
// Generic function to safely deallocate a raw pointer
#[inline]
pub fn deallocate<T: ?Sized>(pointer: Ptr<T>) {
    // safety: Dafny won't call this function unless it can guarantee the object is still allocated
    unsafe {
        // Takes ownership of the reference,
        // so that it's deallocated at the end of the method
        drop(Box::from_raw(pointer.into_raw()));
    }
}

pub struct ExactPool<T: Clone> {
    current: T,
    yielded: bool,
}

// Implement iterator for an exact pool, yielding
impl<T: Clone> Iterator for ExactPool<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        if self.yielded {
            None
        } else {
            self.yielded = true;
            Some(self.current.clone())
        }
    }
}
pub fn exact_range<T: Clone>(value: T) -> ExactPool<T> {
    ExactPool {
        current: value,
        yielded: false,
    }
}

// Any Dafny trait must require classes extending it to have a method "as_any_mut"
// that can convert the reference from that trait to a reference of Any

// 'is' is meant to be used on references only, to check if a trait reference is a class reference
#[macro_export]
macro_rules! is {
    ($raw:expr, $id:ty) => {
        $crate::modify!($crate::cast_any!($raw))
            .downcast_mut::<$id>()
            .is_some()
    };
}

#[macro_export]
macro_rules! is_object {
    ($raw:expr, $id:ty) => {
        $crate::md!($crate::cast_any_object!($raw))
            .downcast_mut::<$id>()
            .is_some()
    };
}

// cast_any is meant to be used on references only, to convert any references (classes or traits)*
// to an Any reference trait
#[macro_export]
macro_rules! cast_any {
    ($raw:expr) => {
        $crate::Upcast::<$crate::DynAny>::upcast($crate::read!($raw))
    };
}
// cast_any_object is meant to be used on references only, to convert any references (classes or traits)*
// to an Any reference trait
#[macro_export]
macro_rules! cast_any_object {
    ($obj:expr) => {
        $crate::UpcastObject::<$crate::DynAny>::upcast($crate::md!($obj))
    };
}

// When initializing an uninitialized field for the first time,
// we ensure we don't drop the previous content
// This is problematic if the same field is overwritten multiple times
/// In that case, prefer to use update_uninit
#[macro_export]
macro_rules! update_field_nodrop {
    ($ptr:expr, $field:ident, $value:expr) => {
        $crate::update_nodrop!($crate::modify!($ptr).$field, $value)
    };
}

// Same as update_field_nodrop but for mutable fields
#[macro_export]
macro_rules! update_field_mut_nodrop {
    ($ptr:expr, $field:ident, $value:expr) => {
        let lhs = $ptr;
        let value = $value;
        unsafe { $crate::read!(lhs).$field.get().write(value) }
    };
}

// When initializing an uninitialized field for the first time,
// we ensure we don't drop the previous content
#[macro_export]
macro_rules! update_nodrop {
    ($ptr:expr, $value:expr) => {
        // safety: Dafny won't call this function unless it can guarantee the value at the address was not
        // yet initialized, so that not dropping it won't create a memory leak
        unsafe { ::std::ptr::addr_of_mut!($ptr).write($value) }
    }
}

// Given a class or array pointer, transforms it to a mutable reference
#[macro_export]
macro_rules! modify {
    ($ptr:expr) => {{
        #[allow(unused_unsafe)]
        let tmp =
            unsafe { &mut *($crate::UnsafeCell::raw_get($ptr.0.unwrap_unchecked().as_ptr())) };
        tmp
    }};
}

// Given a class or array pointer, transforms it to a read-only reference
#[macro_export]
macro_rules! read {
    ($ptr:expr) => {{
        #[allow(unused_unsafe)]
        let tmp = unsafe { &*($crate::UnsafeCell::raw_get($ptr.0.unwrap_unchecked().as_ptr())) };
        tmp
    }};
}

// If the field is guaranteed to be assigned only once, update_field_nodrop is sufficient
#[macro_export]
macro_rules! update_field_uninit {
    ($t:expr, $field:ident, $field_assigned:expr, $value:expr) => {{
        let computed_value = $value;
        #[allow(unused_assignments)]
        if $field_assigned {
            $crate::modify!($t).$field = computed_value;
        } else {
            $crate::update_field_nodrop!($t, $field, computed_value);
            $field_assigned = true;
        }
    }};
}

// Same as update_field_uninit but for mutable fields
#[macro_export]
macro_rules! update_field_mut_uninit {
    ($t:expr, $field:ident, $field_assigned:expr, $value:expr) => {{
        let computed_value = $value;
        #[allow(unused_assignments)]
        if $field_assigned {
            $crate::modify_field!($crate::read!($t).$field, computed_value);
        } else {
            $crate::update_field_mut_nodrop!($t, $field, computed_value);
            $field_assigned = true;
        }
    }};
}

// Macro to call at the end of the first new; constructor when not every field is guaranteed to be assigned.
#[macro_export]
macro_rules! update_field_if_uninit {
    ($t:expr, $field:ident, $field_assigned:expr, $value:expr) => {{
        let computed_value = $value;
        if !$field_assigned {
            $crate::update_field_nodrop!($t, $field, computed_value);
            $field_assigned = true;
        }
    }};
}

// Same as update_field_if_uninit but for mutable fields
#[macro_export]
macro_rules! update_field_mut_if_uninit {
    ($t:expr, $field:ident, $field_assigned:expr, $value:expr) => {{
        let computed_value = $value;
        if !$field_assigned {
            $crate::update_field_mut_nodrop!($t, $field, computed_value);
            $field_assigned = true;
        }
    }};
}

/////////////////
// Raw pointers (require wrapping because of equality)
/////////////////

// This Ptr has the same run-time space as *mut
pub struct Ptr<T: ?Sized>(pub Option<NonNull<UnsafeCell<T>>>);

#[cfg(feature = "sync")]
unsafe impl<T: ?Sized> Send for Ptr<T> {}

#[cfg(feature = "sync")]
unsafe impl<T: ?Sized> Sync for Ptr<T> {}

impl<T: ?Sized> Ptr<T> {
    pub fn null() -> Self {
        Ptr(None)
    }
    pub fn is_null(&self) -> bool {
        self.0.is_none()
    }
    #[inline]
    pub fn from_raw_nonnull(t: *mut T) -> Ptr<T> {
        unsafe {
            Ptr(Some(::std::mem::transmute::<
                NonNull<T>,
                NonNull<UnsafeCell<T>>,
            >(NonNull::new_unchecked(t))))
        }
    }
    pub fn from_box(t: Box<T>) -> Ptr<T> {
        Self::from_raw_nonnull(Box::into_raw(t))
    }
    pub fn into_raw(self) -> *mut T {
        if self.is_null() {
            panic!("Cannot turn a null pointer into a raw pointer");
        }
        let nonnull = unsafe { self.0.unwrap_unchecked() };
        unsafe { ::std::mem::transmute::<_, *mut T>(nonnull.as_ptr()) }
    }
}

impl<T: ?Sized + 'static + Upcast<DynAny>> Ptr<T> {
    pub fn is_instance_of<U: 'static>(self) -> bool {
        if self.is_null() {
            false
        } else {
            read!(Upcast::<DynAny>::upcast(read!(self)))
                .downcast_ref::<U>()
                .is_some()
        }
    }
}

impl<T> NontrivialDefault for Ptr<T> {
    fn nontrivial_default() -> Self {
        // Create a null pointer
        Self::null()
    }
}

impl<T> Ptr<T> {
    pub fn new(val: T) -> Ptr<T> {
        Self::from_box(Box::new(val))
    }
}

impl<T: ?Sized> Eq for Ptr<T> {}

impl<T: ?Sized> Clone for Ptr<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for Ptr<T> {}

impl<T: ?Sized> Default for Ptr<T> {
    fn default() -> Self {
        Ptr::null()
    }
}

impl<T: ?Sized> Debug for Ptr<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_print(f, false)
    }
}
impl<T: ?Sized> DafnyPrint for Ptr<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "<object>")
    }
}

impl<T: ?Sized, U: ?Sized> PartialEq<Ptr<U>> for Ptr<T> {
    fn eq(&self, other: &Ptr<U>) -> bool {
        if !self.is_null() {
            if !other.is_null() {
                // To compare addresses, we need to ensure we only compare thin pointers
                // https://users.rust-lang.org/t/comparing-addresses-between-fat-and-thin-pointers/89008
                ::std::ptr::eq(
                    self.clone().into_raw() as *const (),
                    other.clone().into_raw() as *const (),
                )
            } else {
                false
            }
        } else if !other.is_null() {
            false
        } else {
            true
        }
    }
}

impl<T: ?Sized> Hash for Ptr<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if !self.is_null() {
            (read!(self.clone()) as *const T as *const ()).hash(state);
        } else {
            0.hash(state);
        }
    }
}

impl<T: ?Sized> AsMut<T> for Ptr<T> {
    fn as_mut(&mut self) -> &mut T {
        modify!(self.clone())
    }
}
impl<T: ?Sized> AsRef<T> for Ptr<T> {
    fn as_ref(&self) -> &T {
        read!(self.clone())
    }
}

impl<T: ?Sized> Ptr<T> {
    // Never use on local values, only on &self types previously called on Ptr types.
    pub fn from_ref(r: &T) -> Ptr<T> {
        Ptr(unsafe { ::std::mem::transmute::<_, Option<NonNull<UnsafeCell<T>>>>(r as *const T) })
    }
}
// cast is meant to be used on references only, to downcast a trait reference to a class reference
#[macro_export]
macro_rules! cast {
    ($raw:expr, $id:ty) => {{
        #[allow(unused_unsafe)]
        let tmp = unsafe {
            let expr = $raw;
            let res: $crate::Ptr<$id> = if expr.is_null() {
                $crate::Ptr::null()
            } else {
                $crate::Ptr::from_raw_nonnull(expr.into_raw() as *mut $id)
            };
            res
        };
        tmp
    }};
}

/////////////////
// Reference-counted classes mode
/////////////////

pub struct Object<T: ?Sized>(pub Option<rcmut::RcMut<T>>);

impl<T: ?Sized> Object<T> {
    // For safety, it requires the Rc to have been created with Rc::new()
    pub unsafe fn from_rc(rc: Rc<T>) -> Object<T> {
        unsafe { Object(Some(rcmut::from_rc(rc))) }
    }
    pub fn null() -> Object<T> {
        Object(None)
    }
    pub fn is_null(&self) -> bool {
        self.0.is_none()
    }
}
impl<T: ?Sized + 'static + UpcastObject<DynAny>> Object<T> {
    pub fn is_instance_of<U: 'static>(self) -> bool {
        // safety: Dafny won't call this function unless it can guarantee the object is still allocated
        rd!(UpcastObject::<DynAny>::upcast(rd!(self)))
            .downcast_ref::<U>()
            .is_some()
    }
}
impl<T> Object<T> {
    pub fn new(val: T) -> Object<T> {
        Object(Some(rcmut::new(val)))
    }
}
impl<T: ?Sized> Eq for Object<T> {}

impl<T: ?Sized> Clone for Object<T> {
    fn clone(&self) -> Self {
        Object(self.0.clone())
    }
}

impl<T: ?Sized> Default for Object<T> {
    fn default() -> Self {
        Object(None)
    }
}

impl<T: ?Sized + UpcastObject<DynAny>> Debug for Object<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.fmt_print(f, false)
    }
}
impl<T: ?Sized + UpcastObject<DynAny>> DafnyPrint for Object<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        let obj_any = UpcastObject::<DynAny>::upcast(self.as_ref());
        let option_string = obj_any.as_ref().downcast_ref::<String>();
        match option_string {
            Some(s) => write!(f, "{}", s),
            None => write!(f, "<object>"),
        }
    }
}

impl<T: DafnyType> DafnyPrint for Object<[T]> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "<object>")
    }
}
impl UpcastObject<DynAny> for String {
    fn upcast(&self) -> Object<DynAny> {
        // SAFETY: RC was just created
        unsafe { Object::from_rc(Rc::new(self.clone()) as Rc<DynAny>) }
    }
}

impl<T: ?Sized, U: ?Sized> PartialEq<Object<U>> for Object<T> {
    fn eq(&self, other: &Object<U>) -> bool {
        if let Some(p) = &self.0 {
            if let Some(q) = &other.0 {
                // To compare addresses, we need to ensure we only compare thin pointers
                // https://users.rust-lang.org/t/comparing-addresses-between-fat-and-thin-pointers/89008
                ::std::ptr::eq(p.as_ref().get() as *const (), q.as_ref().get() as *const ())
            } else {
                false
            }
        } else if let Some(_q) = &other.0 {
            false
        } else {
            true
        }
    }
}

impl<T: ?Sized> Hash for Object<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if let Some(p) = &self.0 {
            (p.as_ref().get() as *const ()).hash(state);
        } else {
            0.hash(state);
        }
    }
}

impl<T: ?Sized> AsMut<T> for Object<T> {
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut *(self.0).as_ref().unwrap_unchecked().as_ref().get() }
    }
}
impl<T: ?Sized> AsRef<T> for Object<T> {
    fn as_ref(&self) -> &T {
        unsafe { &*(self.0).as_ref().unwrap_unchecked().as_ref().get() }
    }
}

// Never inline because, when compiling with cargo --release, sometimes it gets rid of this statement
#[inline(never)]
fn increment_strong_count<T: ?Sized>(data: *const T) {
    // SAFETY: This method is called only on values that were constructed from an Rc
    unsafe {
        // Black box avoids the compiler wrongly inferring that increment strong count does nothing since the data it was applied to can be traced to be borrowed
        ::std::hint::black_box(Rc::increment_strong_count(data));
    }
}

impl<T: ?Sized> Object<T> {
    // SAFETY: This function needs to be called from a reference obtained by calling read!(o) on an object
    // We never inline this function, otherwise the compiler might figure out a way to remove the increment_strong_count
    #[inline(never)]
    pub fn from_ref(r: &T) -> Object<T> {
        let pt = r as *const T as *const UnsafeCell<T>;
        // SAFETY: Not guaranteed unfortunately. But looking at the sources of from_raw as of today 10/24/2024
        // it will will correctly rebuilt the Rc
        let rebuilt = ::std::hint::black_box(unsafe { Rc::from_raw(pt) });
        let _previous_strong_count = ::std::hint::black_box(Rc::strong_count(&rebuilt));
        ::std::hint::black_box(increment_strong_count(pt));
        let _new_strong_count = ::std::hint::black_box(Rc::strong_count(&rebuilt));
        #[cfg(not(feature = "sync"))]
        assert_eq!(_new_strong_count, _previous_strong_count + 1); // Will panic if not. Asserted only in sequential mode
        Object(Some(rebuilt))
    }
}

#[macro_export]
macro_rules! cast_object {
    ($raw:expr, $id:ty) => {
        unsafe {
            let res: $crate::Object<$id> = $crate::Object(Some($crate::Rc::from_raw(
                $crate::Rc::into_raw($raw.0.unwrap()) as _,
            )));
            res
        }
    };
}

// Returns an object whose fields are yet initialized. Only use update_field_uninit_object  and update_field_if_uninit_object to initialize fields.
pub fn allocate_object<T>() -> Object<T> {
    unsafe { mem::transmute(object::new::<MaybeUninit<T>>(MaybeUninit::uninit())) }
}

pub struct AllocationTracker {
    allocations: Vec<Weak<DynAny>>,
}

#[cfg(feature = "sync")]
pub fn allocate_object_track<T: 'static + Sync + Send>(
    allocation_tracker: &mut AllocationTracker,
) -> Object<T> {
    let res = allocate_object::<T>();
    allocation_tracker
        .allocations
        .push(Rc::<UnsafeCell<T>>::downgrade(&res.0.clone().unwrap()));
    res
}
#[cfg(not(feature = "sync"))]
pub fn allocate_object_track<T: 'static>(allocation_tracker: &mut AllocationTracker) -> Object<T> {
    let res = allocate_object::<T>();
    allocation_tracker
        .allocations
        .push(Rc::<UnsafeCell<T>>::downgrade(&res.0.clone().unwrap()));
    res
}

// Equivalent of update_field_nodrop but for rcmut
#[macro_export]
macro_rules! update_field_nodrop_object {
    ($ptr:expr, $field: ident, $value:expr) => {
        $crate::update_nodrop_object!(
            ($crate::rcmut::borrow_mut(&mut $ptr.0.clone().unwrap())).$field,
            $value
        )
    };
}

// Same but for mutable fields
#[macro_export]
macro_rules! update_field_mut_nodrop_object {
    ($ptr:expr, $field: ident, $value:expr) => {
        unsafe {
            ($crate::rcmut::borrow_mut(&mut $ptr.0.clone().unwrap()))
                .$field
                .get()
                .write($value)
        }
    };
}

// Equivalent of update_nodrop but for rcmut
#[macro_export]
macro_rules! update_nodrop_object {
    ($ptr:expr, $value:expr) => {
        unsafe { ::std::ptr::addr_of_mut!($ptr).write($value) }
    };
}

// Equivalent of update_field_if_uninit but for rcmut
#[macro_export]
macro_rules! update_field_if_uninit_object {
    ($t:expr, $field:ident, $field_assigned:expr, $value:expr) => {{
        #[allow(unused_assignments)]
        if !$field_assigned {
            let computed_value = $value;
            $crate::update_field_nodrop_object!($t, $field, computed_value);
            $field_assigned = true;
        }
    }};
}

// Same for mutable fields
#[macro_export]
macro_rules! update_field_mut_if_uninit_object {
    ($t:expr, $field:ident, $field_assigned:expr, $value:expr) => {{
        #[allow(unused_assignments)]
        if !$field_assigned {
            let computed_value = $value;
            $crate::update_field_mut_nodrop_object!($t, $field, computed_value);
            $field_assigned = true;
        }
    }};
}

// Equivalent of update_field_uninit but for rcmut
#[macro_export]
macro_rules! update_field_uninit_object {
    ($t:expr, $field:ident, $field_assigned:expr, $value:expr) => {{
        let computed_value = $value;
        #[allow(unused_assignments)]
        if $field_assigned {
            $crate::md!($t).$field = computed_value;
        } else {
            $crate::update_field_nodrop_object!($t, $field, computed_value);
            $field_assigned = true;
        }
    }};
}

// Same but for mutable fields
#[macro_export]
macro_rules! update_field_mut_uninit_object {
    ($t:expr, $field:ident, $field_assigned:expr, $value:expr) => {{
        let computed_value = $value;
        #[allow(unused_assignments)]
        if $field_assigned {
            $crate::modify_field!($crate::rd!($t).$field, computed_value);
        } else {
            $crate::update_field_mut_nodrop_object!($t, $field, computed_value);
            $field_assigned = true;
        }
    }};
}

// Equivalent of modify but for rcmut
#[macro_export]
macro_rules! md {
    ($x:expr) => {
        $x.clone().as_mut()
    };
}

// Equivalent of read but for rcmut
#[macro_export]
macro_rules! rd {
    ($x:expr) => {
        $x.as_ref()
    };
}

// To use when modifying a mutable field that is wrapped with UnsafeCell
#[macro_export]
macro_rules! modify_field {
    ($pointer:expr, $rhs:expr) => {{
        let lhs = $pointer.get();
        let rhs = $rhs;
        unsafe { *lhs = rhs }
    }};
}

// To use when reading a mutable field that is wrapped with UnsafeCell
#[macro_export]
macro_rules! read_field {
    ($pointer:expr) => {{
        let lhs = $pointer.get();
        unsafe { (*lhs).clone() }
    }};
}

pub type Field<T> = UnsafeCell<T>;
pub fn new_field<T>(t: T) -> Field<T> {
    UnsafeCell::new(t)
}

// Count the number of references to the given object
#[macro_export]
macro_rules! refcount {
    ($x:expr) => {
        $crate::Rc::strong_count(unsafe { $crate::rcmut::as_rc($x.0.as_ref().unwrap()) })
    };
}

pub mod object {
    use crate::{Any, DynAny};

    pub fn downcast<T: 'static>(_self: crate::Object<DynAny>) -> crate::Object<T> {
        super::cast_object!(_self, T)
    }

    pub fn new<T>(val: T) -> crate::Object<T> {
        crate::Object(Some(crate::rcmut::new(val)))
    }
    #[inline]
    pub fn is<T: 'static + Any>(_self: crate::Object<DynAny>) -> bool {
        is_object!(_self, T)
    }
}

// Inspired from https://crates.io/crates/rcmut
pub mod rcmut {
    use crate::Rc;
    use crate::UnsafeCell;
    use ::std::mem::{self, MaybeUninit};

    pub fn array_object_from_rc<T>(data: Rc<[T]>) -> crate::Object<[T]> {
        crate::Object(Some(unsafe { from_rc(data) }))
    }
    pub fn array_object_from_box<T>(data: Box<[T]>) -> crate::Object<[T]> {
        let data: Rc<[T]> = data.into();
        crate::Object(Some(unsafe { from_rc(data) }))
    }
    pub struct Array<T> {
        pub data: Box<[T]>,
    }
    impl<T> Array<T> {
        pub fn new(data: Box<[T]>) -> crate::Object<Array<T>> {
            crate::Object(Some(new(Array { data })))
        }

        pub fn placebos_usize_object(length: usize) -> crate::Object<Array<MaybeUninit<T>>> {
            let x = crate::array::placebos_box_usize::<T>(length);
            Array::<MaybeUninit<T>>::new(x)
        }
    }
    /// A reference counted smart pointer with unrestricted mutability.
    pub type RcMut<T> = Rc<UnsafeCell<T>>;

    /// Create a new RcMut for a value.
    pub fn new<T>(val: T) -> RcMut<T> {
        Rc::new(UnsafeCell::new(val))
    }
    /// Retrieve the inner Rc as a reference.
    pub unsafe fn from<T>(value: Box<T>) -> RcMut<T> {
        unsafe { mem::transmute(Rc::new(*value)) }
    }

    pub unsafe fn from_rc<T: ?Sized>(value: Rc<T>) -> RcMut<T> {
        unsafe { mem::transmute(value) }
    }

    pub unsafe fn as_rc<T: ?Sized>(this: &RcMut<T>) -> &Rc<T> {
        unsafe { mem::transmute(this) }
    }
    pub unsafe fn to_rc<T: ?Sized>(this: RcMut<T>) -> Rc<T> {
        unsafe { mem::transmute(this) }
    }

    /// Retrieve the inner Rc as a mutable reference.
    pub unsafe fn as_rc_mut<T: ?Sized>(this: &mut RcMut<T>) -> &mut Rc<T> {
        unsafe { mem::transmute(this) }
    }

    /// Get a reference to the value.
    #[inline]
    pub unsafe fn borrow<T: ?Sized>(this: &RcMut<T>) -> &T {
        unsafe { &*this.get() }
    }

    /// Get a mutable reference to the value.
    #[inline]
    pub unsafe fn borrow_mut<T: ?Sized>(this: &mut RcMut<T>) -> &mut T {
        unsafe { &mut *this.get() }
    }

    #[cfg(feature = "sync")]
    pub unsafe fn downcast<T: 'static + Send + Sync>(
        this: RcMut<crate::DynAny>,
    ) -> Option<RcMut<T>> {
        let t: Rc<crate::DynAny> = unsafe { to_rc(this) };
        let t: Rc<T> = Rc::downcast::<T>(t).ok()?;
        unsafe { mem::transmute(t) }
    }

    #[cfg(not(feature = "sync"))]
    pub unsafe fn downcast<T: 'static>(this: RcMut<crate::DynAny>) -> Option<RcMut<T>> {
        let t: Rc<crate::DynAny> = unsafe { to_rc(this) };
        let t: Rc<T> = Rc::downcast::<T>(t).ok()?;
        unsafe { mem::transmute(t) }
    }
}

/////////////////
// Method helpers
/////////////////

// A MaybePlacebo is a value that is either a placebo or a real value.
// It is a wrapper around a MaybeUninit<T> value, but knowing whether the value is a placebo or not.
// That way, when it is dropped, the underlying value is only dropped if it is not a placebo.

#[derive(Clone)]
pub struct MaybePlacebo<T>(Option<T>);
impl<T: Clone> MaybePlacebo<T> {
    #[inline]
    pub fn read(&self) -> T {
        // safety: Dafny will guarantee we will never read a placebo value
        unsafe { self.0.clone().unwrap_unchecked() }
    }
}

impl<T> MaybePlacebo<T> {
    #[inline]
    pub fn new() -> Self {
        MaybePlacebo(None)
    }
    #[inline]
    pub fn from(v: T) -> Self {
        MaybePlacebo(Some(v))
    }
}

#[macro_export]
macro_rules! tuple_extract_index {
    ($x:expr, $i:expr) => {
        $x.$i
    };
}

// A macro that maps tuple (a, b, c...) to produce (MaybePlacebo::from(a), MaybePlacebo::from(b), MaybePlacebo::from(c))
// maybe_placebos_from!(expr, 0, 1, 2, 3)
// = let x = expr;
//   (MaybePlacebo::from(x.0), MaybePlacebo::from(x.1), MaybePlacebo::from(x.2), MaybePlacebo::from(x.3))
#[macro_export]
macro_rules! maybe_placebos_from {
    ($x:expr, $($i:tt), *) => {
        {
            let x = $x;
            (
                $( $crate::MaybePlacebo::from(x.$i), )*
            )
        }
    }
}

////////////////
// Coercion
////////////////

pub fn upcast_object<A: ?Sized, B: ?Sized>() -> Rc<impl Fn(Object<A>) -> Object<B>>
where
    A: UpcastObject<B>,
{
    Rc::new(|x: Object<A>| x.as_ref().upcast())
}

pub fn upcast<A: ?Sized, B: ?Sized>() -> Rc<impl Fn(Ptr<A>) -> Ptr<B>>
where
    A: Upcast<B>,
{
    Rc::new(|x: Ptr<A>| read!(x).upcast())
}

pub fn upcast_box<A, B: ?Sized>() -> Rc<impl Fn(A) -> Box<B>>
where
    A: UpcastBox<B>,
{
    Rc::new(|x: A| UpcastBox::upcast(&x))
}
pub fn upcast_box_box<A: ?Sized, B: ?Sized>() -> Rc<impl Fn(Box<A>) -> Box<B>>
where
    A: UpcastBox<B>,
{
    Rc::new(|x: Box<A>| UpcastBox::upcast(x.as_ref()))
}

pub fn upcast_id<A>() -> Rc<impl Fn(A) -> A> {
    Rc::new(|x: A| x)
}

pub fn rc_coerce<T: Clone, U: Clone>(f: Rc<impl Fn(T) -> U>) -> Rc<impl Fn(Rc<T>) -> Rc<U>> {
    Rc::new(move |x: Rc<T>| Rc::new(f.as_ref()(x.as_ref().clone())))
}
pub fn box_coerce<T: Clone, U: Clone>(f: Box<impl Fn(T) -> U>) -> Box<impl Fn(Box<T>) -> Box<U>> {
    Box::new(move |x: Box<T>| Box::new(f.as_ref()(x.as_ref().clone())))
}

pub fn fn1_coerce<T: Clone + 'static, A: Clone + 'static, R: Clone + 'static>(
    a_to_r: Rc<impl Fn(A) -> R + 'static>,
) -> Rc<impl Fn(Rc<dyn Fn(&T) -> A>) -> Rc<dyn Fn(&T) -> R> + 'static> {
    Rc::new(move |t_to_a: Rc<dyn Fn(&T) -> A>| {
        let a_to_r = a_to_r.clone();
        let t_to_a = t_to_a.clone();
        let r: Rc<dyn Fn(&T) -> R + 'static> = Rc::new(move |t: &T| a_to_r(t_to_a(t)));
        r
    })
}

// For pointers
pub trait Upcast<T: ?Sized> {
    fn upcast(&self) -> Ptr<T>;
}
pub trait UpcastObject<T: ?Sized> {
    fn upcast(&self) -> Object<T>;
}
impl<T: ?Sized> Upcast<T> for T {
    fn upcast(&self) -> Ptr<T> {
        Ptr::from_raw_nonnull(self as *const T as *mut T)
    }
}
impl<T: ?Sized> UpcastObject<T> for T {
    fn upcast(&self) -> Object<T> {
        Object::from_ref(self)
    }
}

// For general traits
pub trait UpcastBox<T: ?Sized> {
    fn upcast(&self) -> Box<T>;
}

impl<T: ?Sized, U> UpcastBox<T> for Rc<U>
where
    U: UpcastBox<T>,
{
    fn upcast(&self) -> Box<T> {
        UpcastBox::upcast(AsRef::as_ref(self))
    }
}

pub trait AnyRef {
    fn as_any_ref(&self) -> &dyn Any;
}

impl<T: 'static> AnyRef for T {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }
}

#[macro_export]
macro_rules! Extends {
    ($traitType: tt) => {
        $traitType + ::dafny_runtime::Upcast<dyn $traitType>
    }
}

#[macro_export]
macro_rules! UpcastFn {
    ($B:ty) => {
        fn upcast(&self) -> $crate::Ptr<$B> {
            $crate::Ptr::from_raw_nonnull(self as *const Self as *mut Self as *mut $B)
        }
    };
}

#[macro_export]
macro_rules! UpcastObjectFn {
    ($B:ty) => {
        fn upcast(&self) -> $crate::Object<$B> {
            $crate::Object::from_ref(self as &$B)
        }
    };
}

// It works only when there is no type parameters for $A...
#[macro_export]
macro_rules! UpcastDef {
    ($A:ty, $B:ty) => {
        impl $crate::Upcast<$B> for $A {
            $crate::UpcastFn!($B);
        }
    };

    ($A:ty, $B:ty, $($C: ty),*) => {
        $crate::UpcastDef!($A, $B);
        $crate::UpcastDef!($A, $($C),*);
    }
}

#[macro_export]
macro_rules! UpcastDefObject {
    ($A:ty, $B:ty) => {
        impl $crate::UpcastObject<$B> for $A {
            $crate::UpcastObjectFn!($B);
        }
    };

    ($A:ty, $B:ty, $($C: ty),*) => {
        $crate::UpcastDefObject!($A, $B);
        $crate::UpcastDefObject!($A, $($C),*);
    }
}

// Coercions for sets
impl<U: DafnyTypeEq> Set<U> {
    pub fn coerce<V: DafnyTypeEq>(f: Rc<impl Fn(U) -> V>) -> Rc<impl Fn(Set<U>) -> Set<V>> {
        Rc::new(move |x: Set<U>| {
            // We need to upcast individual elements
            let f2 = f.clone();
            let mut new_set: HashSet<V> = HashSet::<V>::default();
            for value in x.data.iter() {
                new_set.insert(f2(value.clone()));
            }
            Set::from_hashset_owned(new_set)
        })
    }
}

// Coercions for sequences
impl<U: DafnyType> Sequence<U> {
    pub fn coerce<V: DafnyType>(f: Rc<impl Fn(U) -> V>) -> Rc<impl Fn(Sequence<U>) -> Sequence<V>> {
        // We need to upcast individual elements
        Rc::new(move |x: Sequence<U>| {
            let mut new_seq: Vec<V> = Vec::<V>::default();
            let f2 = f.clone();
            for value in x.to_array().iter() {
                new_seq.push(f2(value.clone()));
            }
            Sequence::from_array_owned(new_seq)
        })
    }
}

// Coercions for multisets
impl<U: DafnyTypeEq> Multiset<U> {
    pub fn coerce<V: DafnyTypeEq>(
        f: Rc<impl Fn(U) -> V>,
    ) -> Rc<impl Fn(Multiset<U>) -> Multiset<V>> {
        // We need to upcast individual elements
        Rc::new(move |x: Multiset<U>| {
            let f2 = f.clone();
            // We need to upcast individual elements
            let mut new_multiset: HashMap<V, DafnyInt> = HashMap::<V, DafnyInt>::default();
            for (value, count) in x.data.into_iter() {
                new_multiset.insert(f2(value), count.clone());
            }
            Multiset::from_hashmap_owned(new_multiset)
        })
    }
}

// Coercions for Maps
impl<K: DafnyTypeEq, U: DafnyTypeEq> Map<K, U> {
    pub fn coerce<V: DafnyTypeEq>(f: Rc<impl Fn(U) -> V>) -> Rc<impl Fn(Map<K, U>) -> Map<K, V>> {
        // We need to upcast individual elements
        Rc::new(move |x: Map<K, U>| {
            let f2 = f.clone();
            let mut new_map: HashMap<K, V> = HashMap::<K, V>::default();
            for (key, value) in x.data.iter() {
                new_map.insert(key.clone(), f2(value.clone()));
            }
            Map::from_hashmap_owned(new_map)
        })
    }
}

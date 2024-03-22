#[cfg(test)]
mod tests;
use std::{fmt::{Display, Formatter},
          rc::Rc, ops::{Deref, Add},
          collections::{HashSet, HashMap},
          cell::RefCell, any::Any};
use num::{Integer, Signed, One};
use as_any::AsAny;

pub use once_cell::unsync::Lazy;

pub use num::bigint::BigInt;
pub use num::rational::BigRational;
pub use num::FromPrimitive;
pub use num::NumCast;
pub use num::Zero;
pub use itertools;

// An atomic box is just a RefCell in Rust
pub type SizeT = usize;

/******************************************************************************
 * Sequences
 ******************************************************************************/

// Three elements
// ArraySequence(var isString: bool, nodeCount: SizeT, immutable_array)
// ConcatSequence(var isString: bool, nodeCount: SizeT, left: Sequence, right: Sequence)
// LazySequence(length: BigInteger, box: RefCell<Rc<Sequence<T>>>)
// We use the named version using {...}, and use snake_case format

// The T must be either a *const T (allocated) OR a Reference Counting (immutable)

#[allow(dead_code)]
mod dafny_runtime_conversions {
    use num::BigInt;

    use crate::Sequence;
    use crate::Map;
    use std::cell::RefCell;
    use std::collections::HashMap;
    use std::rc::Rc;
    use std::hash::Hash;
    pub fn dafny_int_to_bigint(i: &Rc<BigInt>) -> BigInt {
        i.as_ref().clone()
    }
    pub fn bigint_to_dafny_int(i: &BigInt) -> Rc<BigInt> {
        Rc::new(i.clone())
    }

    pub fn dafny_sequence_to_vec<T, X>(s: &Sequence<T>, elem_converter: fn(&T) -> X) -> Vec<X>
      where T: Clone
    {
        let mut array: Vec<T> = Vec::with_capacity(s.cardinality());
        Sequence::<T>::append_recursive(&mut array, s);
        array.iter().map(|x| elem_converter(x)).collect()
    }

    // Used for external conversions
    pub fn vec_to_dafny_sequence<T, X>(array: &Vec<X>, elem_converter: fn(&X) -> T) -> Rc<Sequence<T>>
      where T: Clone
    {
        let mut result: Vec<T> = Vec::with_capacity(array.len());
        for elem in array.iter() {
            result.push(elem_converter(elem));
        }
        Sequence::<T>::new_array_sequence(&Rc::new(result))
    }
    
    fn dafny_map_to_hashmap<K, V, K2, V2>(m: &Rc<Map<K, V>>, converter_k: fn(&K)->K2, converter_v: fn(&V)->V2) -> HashMap<K2, V2>
      where
          K: Eq + Clone + Hash, V: Clone,
          K2: Eq + Hash, V2: Clone
    {
        m.to_hashmap_owned(converter_k, converter_v)
    }

    fn hashmap_to_dafny_map<K2, V2, K, V>(map: &HashMap<K2, V2>, converter_k: fn(&K2)->K, converter_v: fn(&V2)->V)
        -> Rc<Map<K, V>>
      where
        K: Eq + Clone + Hash, V: Clone,
        K2: Eq + Hash, V2: Clone
    {
        let mut result: Vec<(K, V)> = Vec::new();
        for (k, v) in map.iter() {
            result.push((converter_k(k), converter_v(v)));
        }
        let s = Sequence::<(K, V)>::new_array_sequence(&Rc::new(result));
        Rc::new(Map {
            data: s,
            cache: RefCell::new(None)
        })
    }

    // --unicode-chars:true
    pub mod unicode_chars_true {
        use crate::Sequence;
        use std::rc::Rc;

        pub fn string_to_dafny_string(s: &str) -> Rc<Sequence<char>> {
            Sequence::new_array_sequence(&Rc::new(s.chars().collect()))
        }
        pub fn dafny_string_to_string(s: &Rc<Sequence<char>>) -> String {
            let characters = s.to_array();
            characters.iter().collect::<String>()
        }
    }
    
    // --unicode-chars:false
    pub mod unicode_chars_false {
        use crate::Sequence;
        use std::rc::Rc;
        pub fn string_to_dafny_string(s: &str) -> Rc<Sequence<u16>> {
            Sequence::new_array_sequence(&Rc::new(s.encode_utf16().collect()))
        }
        pub fn dafny_string_to_string(s: &Rc<Sequence<u16>>) -> String {
            let characters = s.to_array();
            String::from_utf16(&characters).unwrap()
        }
    }
    
}

#[allow(dead_code)]
enum Sequence<T>
  where T: Clone,
{
    ArraySequence {
        // Values could be a native array because we will know statically that all 
        // accesses are in bounds when using this data structure
        values: Rc<Vec<T>>,
    },
    ConcatSequence {
        left: Rc<Sequence<T>>,
        right: Rc<Sequence<T>>,
        length: SizeT,
    },
    LazySequence {
        length: SizeT,
        boxed: RefCell<Rc<Sequence<T>>>
    }
}

#[allow(dead_code)]
impl <T> Sequence<T>
where T: Clone {
    fn new_array_sequence(values: &Rc<Vec<T>>) -> Rc<Sequence<T>> {        
        Rc::new(Sequence::ArraySequence {
            values: Rc::clone(values),
        })
    }
    fn new_concat_sequence(left: &Rc<Sequence<T>>, right: &Rc<Sequence<T>>) -> Rc<Sequence<T>> {
       Rc::new(Sequence::ConcatSequence {
            left: Rc::clone(&left),
            right: Rc::clone(&right),
            length: left.cardinality() + right.cardinality(),
        })
    }
    fn new_lazy_sequence(boxed: &Rc<Sequence<T>>) -> Rc<Sequence<T>> {
        Rc::new(Sequence::LazySequence {
            length: boxed.cardinality(),
            boxed: RefCell::new(Rc::clone(boxed)),
        })
    }

    fn to_array(&self) -> Rc<Vec<T>> {
        // We convert the match above to statements using the Rust "it" idiom
        if let Sequence::ArraySequence { values, .. } = self {
            // The length of the elements
            Rc::clone(values)
        } else if let Sequence::ConcatSequence { length, .. } = self {
            let mut array: Vec<T> = Vec::with_capacity(*length);
            Sequence::<T>::append_recursive(&mut array, self);
            Rc::new(array)
        } else if let Sequence::LazySequence { boxed, ..  } = self {
            let result = boxed.borrow().to_array();
            // Put the value back into boxed
            boxed.replace(Rc::clone(
                &Sequence::<T>::new_array_sequence(&result)));
            result
        } else {
            panic!("This should never happen")
        }
    }

    fn append_recursive(array: &mut Vec<T>, this: &Sequence<T>) {
        match this {
            Sequence::ArraySequence { values, .. } =>
              // The length of the elements
              for value in values.iter() {
                array.push(value.clone());
              },
            Sequence::ConcatSequence { left, right, .. } =>
              // Let's create an array of size length and fill it up recursively
              {
                Sequence::<T>::append_recursive(array, left);
                Sequence::<T>::append_recursive(array, right);
              }
            Sequence::LazySequence { boxed, .. } =>
            Sequence::<T>::append_recursive(array, boxed.borrow().as_ref()),
        }
    }

    /// Returns the cardinality of this [`Sequence<T>`].
    // The cardinality returns the length of the sequence
    fn cardinality(&self) -> SizeT {
        match self {
            Sequence::ArraySequence { values, .. } =>
              // The length of the elements
              values.len(),
            Sequence::ConcatSequence { length, .. } =>
              *length,
            Sequence::LazySequence { length, .. } =>
              *length,
        }
    }
    fn select(&self, index: SizeT) -> T {
        let array = self.to_array();
        array[index].clone()
    }
    
}

// **************
// Immutable maps
// **************

#[allow(dead_code)]
struct Map<K, V> 
  where K: Clone + Eq + std::hash::Hash, V: Clone
{
    data: Rc<Sequence<(K, V)>>,
    // Any time we explicitly access this map, we index the data
    cache: RefCell<Option<HashMap<K, V>>>
}

#[allow(dead_code)]
impl <K, V> Map<K, V>
  where K: Clone + Eq + std::hash::Hash, V: Clone
{
    fn new_empty() -> Rc<Map<K, V>> {
        Rc::new(Map {
            data: Sequence::new_array_sequence(&Rc::new(Vec::new())),
            cache: RefCell::new(None)
        })
    }
    fn new_from_sequence(data: &Rc<Sequence<(K, V)>>) -> Rc<Map<K, V>> {
        Rc::new(Map {
            data: Rc::clone(data),
            cache: RefCell::new(None)
        })
    }
    fn to_hashmap_owned<K2, V2>(&self, converter_k: fn(&K)->K2, converter_v: fn(&V)->V2) -> HashMap<K2, V2>
      where K2: Eq + std::hash::Hash, V2: Clone
    {
        let mut result: HashMap<K2, V2> = HashMap::new();
        for (k, v) in self.data.to_array().iter() {
            result.insert(converter_k(k), converter_v(v));
        }
        result
    }
    fn compute_hashmap(&self) {
        let mut cache = self.cache.borrow_mut();
        if cache.is_none() {
            *cache = Some(self.to_hashmap_owned(
                |x| x.clone(),
                |x| x.clone()
            ));
        }
    }
    // Dafny will normally guarantee that the key exists.
    fn get(&self, key: &K) -> V {
        self.compute_hashmap();
        self.cache.borrow_mut().as_ref().unwrap().get(key).unwrap().clone()
    }
    fn add(&self, key: K, value: V) -> Rc<Map<K, V>> {
        let new_data = Sequence::<(K, V)>::new_array_sequence(
            &Rc::new(vec![(key, value)]));
        let combined_data = Sequence::<(K, V)>::new_concat_sequence(
            &self.data, &new_data);
        Rc::new(Map {
            data: combined_data,
            cache: RefCell::new(None)
        })
    }
    fn add_multiple(&self, other: &Rc<Map<K, V>>) -> Rc<Map<K, V>> {
        let new_data = Rc::clone(&other.data);
        let combined_data = Sequence::<(K, V)>::new_concat_sequence(
            &self.data, &new_data);
        Rc::new(Map {
            data: combined_data,
            cache: RefCell::new(None)
        })
    
    }
    // TODO: Remaining methods + check names
}

// Generic function to allocate and return a raw pointer immediately
#[inline]
pub fn allocate<T>(value: Box<T>) -> *const T {
    Box::into_raw(value)
}

// Generic function to safely deallocate a raw pointer
#[inline]
pub fn deallocate<T : ?Sized>(pointer: *const T) {
    unsafe {
        // Takes ownership of the reference,
        // so that it's deallocated at the end of the method
        let _ = Box::from_raw(pointer as *mut T);
    }
}

pub fn is_instance_of<T: ?Sized + Any, U: 'static>(theobject: *const T) -> bool {
    unsafe { &*theobject }.as_any().downcast_ref::<U>().is_some()
}

pub fn dafny_rational_to_int(r: &BigRational) -> BigInt {
    euclidian_division(r.numer().clone(), r.denom().clone())
}

pub fn nullable_referential_equality<T: ?Sized>(left: Option<Rc<T>>, right: Option<Rc<T>>) -> bool {
    match (left, right) {
        (Some(l), Some(r)) => {
            Rc::ptr_eq(&l, &r)
        }
        (None, None) => true,
        _ => false
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

impl <A: Add<Output = A> + One + Ord + Clone> Iterator for IntegerRange<A> {
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

pub fn integer_range<A: Add<Output = A> + One + Ord + Clone>(low: A, hi: A) -> impl Iterator<Item = A> {
    IntegerRange {
        hi,
        current: low
    }
}

pub struct LazyFieldWrapper<A>(pub Lazy<A, Box<dyn 'static + FnOnce() -> A>>);

impl <A: PartialEq> PartialEq for LazyFieldWrapper<A> {
    fn eq(&self, other: &Self) -> bool {
        self.0.deref() == other.0.deref()
    }
}

impl <A: Default + 'static> Default for LazyFieldWrapper<A> {
    fn default() -> Self {
        Self(Lazy::new(Box::new(A::default)))
    }
}

impl <A: DafnyPrint> DafnyPrint for LazyFieldWrapper<A> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        self.0.deref().fmt_print(f, in_seq)
    }
}

pub struct FunctionWrapper<A: ?Sized>(pub A);
impl <A> DafnyPrint for FunctionWrapper<A> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "<function>")
    }
}

impl <A: Clone> Clone for FunctionWrapper<A> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl <A> DafnyErasable for FunctionWrapper<A> {
    type Erased = FunctionWrapper<A>;

    fn erase(&self) -> &Self::Erased {
        self
    }

    fn erase_owned(self) -> Self::Erased {
        self
    }
}

impl <A> DafnyUnerasable<FunctionWrapper<A>> for FunctionWrapper<A> {
    fn unerase(v: &FunctionWrapper<A>) -> &Self {
        v
    }

    fn unerase_owned(v: FunctionWrapper<A>) -> Self {
        v
    }
}

impl <A: ?Sized> PartialEq for FunctionWrapper<Rc<A>> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

pub struct DafnyPrintWrapper<T>(pub T);
impl <T: DafnyPrint> Display for DafnyPrintWrapper<&T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt_print(f, false)
    }
}

pub trait DafnyErasable: DafnyUnerasable<Self::Erased>
where Self: Sized {
    type Erased;

    fn erase(&self) -> &Self::Erased {
        unsafe { &*(self as *const Self as *const Self::Erased) }
    }

    fn erase_owned(self) -> Self::Erased {
        unsafe { transmute_unchecked(self) }
    }
}

pub trait DafnyUnerasable<T>
where Self: Sized {
    fn unerase(v: &T) -> &Self {
        unsafe { &*(v as *const T as *const Self) }
    }

    fn unerase_owned(v: T) -> Self {
        unsafe { transmute_unchecked(v) }
    }
}

impl <T: DafnyErasable> DafnyErasable for Option<T> {
    type Erased = Option<T::Erased>;

    #[inline]
    fn erase(&self) -> &Self::Erased {
        unsafe { &*(self as *const Self as *const Self::Erased) }
    }

    #[inline]
    fn erase_owned(self) -> Self::Erased {
        unsafe { transmute_unchecked(self) }
    }
}

impl <T: DafnyUnerasable<U>, U> DafnyUnerasable<Option<U>> for Option<T> {
    #[inline]
    fn unerase(v: &Option<U>) -> &Self {
        unsafe { &*(v as *const Option<U> as *const Self) }
    }

    #[inline]
    fn unerase_owned(v: Option<U>) -> Self {
        unsafe { transmute_unchecked(v) }
    }
}

impl <T: DafnyErasable> DafnyErasable for Rc<T> {
    type Erased = Rc<T::Erased>;

    #[inline]
    fn erase(&self) -> &Self::Erased {
        unsafe { &*(self as *const Self as *const Self::Erased) }
    }

    #[inline]
    fn erase_owned(self) -> Self::Erased {
        unsafe { transmute_unchecked(self) }
    }
}

impl <T: DafnyUnerasable<U>, U> DafnyUnerasable<Rc<U>> for Rc<T> {
    #[inline]
    fn unerase(v: &Rc<U>) -> &Self {
        unsafe { &*(v as *const Rc<U> as *const Self) }
    }

    #[inline]
    fn unerase_owned(v: Rc<U>) -> Self {
        unsafe { transmute_unchecked(v) }
    }
}

impl <T: DafnyErasable> DafnyErasable for Vec<T> {
    type Erased = Vec<T::Erased>;
}

impl <T: DafnyUnerasable<U>, U> DafnyUnerasable<Vec<U>> for Vec<T> {}

impl <T> DafnyErasable for HashSet<T> {
    type Erased = HashSet<T>;

    #[inline]
    fn erase(&self) -> &Self::Erased {
        self
    }

    #[inline]
    fn erase_owned(self) -> Self::Erased {
        self
    }
}

impl <T> DafnyUnerasable<HashSet<T>> for HashSet<T> {
    #[inline]
    fn unerase(v: &HashSet<T>) -> &Self {
        v
    }

    #[inline]
    fn unerase_owned(v: HashSet<T>) -> Self {
        v
    }
}

impl <K, V> DafnyErasable for HashMap<K, V> {
    type Erased = HashMap<K, V>;

    #[inline]
    fn erase(&self) -> &Self::Erased {
        self
    }

    #[inline]
    fn erase_owned(self) -> Self::Erased {
        self
    }
}

impl <K, V> DafnyUnerasable<HashMap<K, V>> for HashMap<K, V> {
    #[inline]
    fn unerase(v: &HashMap<K, V>) -> &Self {
        v
    }

    #[inline]
    fn unerase_owned(v: HashMap<K, V>) -> Self {
        v
    }
}

impl <T> DafnyErasable for Box<T> {
    type Erased = Box<T>;

    #[inline]
    fn erase(&self) -> &Self::Erased {
        self
    }

    #[inline]
    fn erase_owned(self) -> Self::Erased {
        self
    }
}

impl <T> DafnyUnerasable<Box<T>> for Box<T> {
    #[inline]
    fn unerase(v: &Box<T>) -> &Self {
        v
    }

    #[inline]
    fn unerase_owned(v: Box<T>) -> Self {
        v
    }
}

impl <T: DafnyErasable> DafnyErasable for RefCell<T> {
    type Erased = RefCell<T::Erased>;
}

impl <T: DafnyUnerasable<U>, U> DafnyUnerasable<RefCell<U>> for RefCell<T> {}

macro_rules! impl_already_erased {
    ($name:ty) => {
        impl DafnyErasable for $name {
            type Erased = $name;

            #[inline]
            fn erase(&self) -> &Self::Erased {
                self
            }

            #[inline]
            fn erase_owned(self) -> Self::Erased {
                self
            }
        }

        impl DafnyUnerasable<$name> for $name {
            #[inline]
            fn unerase(v: &$name) -> &Self {
                v
            }
        
            #[inline]
            fn unerase_owned(v: $name) -> Self {
                v
            }
        }
    };
}

impl_already_erased! { String }
impl_already_erased! { char }
impl_already_erased! { bool }
impl_already_erased! { u8 }
impl_already_erased! { u16 }
impl_already_erased! { u32 }
impl_already_erased! { u64 }
impl_already_erased! { u128 }
impl_already_erased! { i8 }
impl_already_erased! { i16 }
impl_already_erased! { i32 }
impl_already_erased! { i64 }
impl_already_erased! { i128 }
impl_already_erased! { f32 }
impl_already_erased! { f64 }
impl_already_erased! { () }
impl_already_erased! { BigInt }
impl_already_erased! { BigRational }

// from gazebo
#[inline]
unsafe fn transmute_unchecked<A, B>(x: A) -> B {
    assert_eq!(std::mem::size_of::<A>(), std::mem::size_of::<B>());
    debug_assert_eq!(0, (&x as *const A).align_offset(std::mem::align_of::<B>()));
    let b = std::ptr::read(&x as *const A as *const B);
    std::mem::forget(x);
    b
}

macro_rules! impl_tuple_erased {
    ($($items:ident)*) => {
        impl <$($items,)*> DafnyErasable for ($($items,)*)
        where
            $($items: DafnyErasable,)*
        {
            type Erased = ($($items::Erased,)*);

            #[inline]
            fn erase(&self) -> &Self::Erased {
                unsafe { &*(self as *const Self as *const Self::Erased) }
            }

            #[inline]
            fn erase_owned(self) -> Self::Erased {
                unsafe { transmute_unchecked(self) }
            }
        }

        paste::item! {
            impl <$([<T $items>],)* $($items: DafnyUnerasable<[<T $items>]>,)*> DafnyUnerasable<($([<T $items>],)*)> for ($($items,)*)
            {
                #[inline]
                fn unerase(v: &($([<T $items>],)*)) -> &Self {
                    unsafe { &*(v as *const ($([<T $items>],)*) as *const Self) }
                }

                #[inline]
                fn unerase_owned(v: ($([<T $items>],)*)) -> Self {
                    unsafe { transmute_unchecked(v) }
                }
            }
        }
    };
}

macro_rules! impl_tuple_erased_loop {
    () => {};
    ($first:ident $($rest:ident)*) => {
        impl_tuple_erased_loop! { $($rest)* }
        impl_tuple_erased! { $first $($rest)* }
    };
}

// 32 elements ought to be enough for everyone
impl_tuple_erased_loop! {
    A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 A10
    A11 A12 A13 A14 A15 A16 A17 A18 A19 A20
    A21 A22 A23 A24 A25 A26 A27 A28 A29 A30
    A31
}

pub trait DafnyPrint {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result;

    // Vec<char> gets special treatment so we carry that information here
    #[inline]
    fn is_char() -> bool {
        false
    }
}

impl <T> DafnyPrint for *const T {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "<{} object>", std::any::type_name::<T>())
    }
}

macro_rules! impl_print_display {
    ($name:ty) => {
        impl DafnyPrint for $name {
            fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
                self.fmt(f)
            }
        }
    };
}

impl_print_display! { String }
impl_print_display! { &str }
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

impl DafnyPrint for char {
    #[inline]
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        if in_seq {
            write!(f, "{}", self)
        } else {
            write!(f, "'{}'", self)
        }
    }

    #[inline]
    fn is_char() -> bool {
        true
    }
}

impl <T: DafnyPrint> DafnyPrint for Option<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        match self {
            Some(x) => x.fmt_print(f, false),
            None => write!(f, "null")
        }
    }
}

impl DafnyPrint for BigInt {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

fn divides_a_power_of_10(mut i: BigInt) -> (bool, BigInt, usize) {
    let one: BigInt = One::one();

    let mut factor = one.clone();
    let mut log10 = 0;

    let zero = Zero::zero();
    let ten = BigInt::from_i32(10).unwrap();

    if i <= zero {
        return (false, factor, log10);
    }

    while i.is_multiple_of(&ten) {
        i /= BigInt::from_i32(10).unwrap();
        log10 += 1;
    }

    let two = BigInt::from_i32(2).unwrap();
    let five = BigInt::from_i32(5).unwrap();

    while i.is_multiple_of(&five) {
        i /= &five;
        factor *= &two;
        log10 += 1;
    }

    while i.is_multiple_of(&two) {
        i /= &two;
        factor *= &two;
        log10 += 1;
    }

    (i == one, factor, log10)
}

impl DafnyPrint for BigRational {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        if self.denom() == &One::one() || self.numer() == &Zero::zero() {
            write!(f, "{}.0", self.numer())
        } else {
            let (divides, factor, log10) = divides_a_power_of_10(self.denom().clone());
            if divides {
                let mut num = self.numer().clone();
                num *= factor;

                if num.is_negative() {
                    write!(f, "-")?;
                    num = -num;
                }

                let digits = num.to_string();

                if log10 < digits.len() {
                    let digit_count = digits.len() - log10;
                    write!(f, "{}", &digits[..digit_count])?;
                    write!(f, ".")?;
                    write!(f, "{}", &digits[digit_count..])
                } else {
                    let z = log10 - digits.len();
                    write!(f, "0.")?;
                    for _ in 0..z {
                        write!(f, "0")?;
                    }
                    write!(f, "{}", digits)
                }
            } else {
                write!(f, "({}.0 / {}.0)", self.numer(), self.denom())
            }
        }
    }
}

impl <T: DafnyPrint> DafnyPrint for Rc<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        self.as_ref().fmt_print(f, in_seq)
    }
}

impl <T: DafnyPrint> DafnyPrint for Vec<T> {
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

impl <T: DafnyPrint> DafnyPrint for RefCell<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        self.borrow().fmt_print(f, _in_seq)
    }
}

impl <T: DafnyPrint> DafnyPrint for HashSet<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{{")?;

        let mut i = 0;

        for item in self.iter() {
            if i > 0 {
                write!(f, ", ")?;
            }

            item.fmt_print(f, false)?;

            i += 1;
        }

        write!(f, "}}")
    }
}

macro_rules! impl_tuple_print {
    ($($items:ident)*) => {
        impl <$($items,)*> DafnyPrint for ($($items,)*)
        where
            $($items: DafnyPrint,)*
        {
            #[allow(unused_assignments)]
            fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
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

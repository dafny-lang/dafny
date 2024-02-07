#[cfg(test)]
mod tests;
use std::{any::Any, borrow::Borrow, cell::{RefCell, UnsafeCell}, cmp::Ordering, collections::{HashMap, HashSet}, fmt::{Display, Formatter}, hash::{Hash, Hasher}, ops::{Add, Deref, Div, Mul, Neg, Rem, Sub}, rc::Rc};
use num::{bigint::ParseBigIntError, Integer, Num, One, Signed, ToPrimitive};

pub use once_cell::unsync::Lazy;

pub use num::bigint::BigInt;
pub use num::rational::BigRational;
pub use num::FromPrimitive;
pub use num::NumCast;
pub use num::Zero;
pub use itertools;

// An atomic box is just a RefCell in Rust
pub type SizeT = usize;

// Dafny types must be clonable in constant time
pub trait DafnyType: Clone + DafnyPrint {}
pub trait DafnyTypeEq: DafnyType + Hash + Eq {}


/******************************************************************************
 * Sequences
 ******************************************************************************/

// Three elements
// ArraySequence(var isString: bool, nodeCount: SizeT, immutable_array)
// ConcatSequence(var isString: bool, nodeCount: SizeT, left: Sequence, right: Sequence)
// LazySequence(length: BigInteger, box: RefCell<Rc<Sequence<T>>>)
// We use the named version using {...}, and use snake_case format

// The T must be either a *const T (allocated) OR a Reference Counting (immutable)
pub mod dafny_runtime_conversions {
    use crate::DafnyType;
    use crate::DafnyTypeEq;
    pub type DafnyInt = crate::DafnyInt;
    pub type DafnySequence<T> = crate::Sequence<T>;
    pub type DafnyMap<K, V> = crate::Map<K, V>;
    pub type DafnySet<T> = crate::Set<T>;
    pub type DafnyMultiset<T> = crate::Multiset<T>;
    pub type DafnyBool = bool;
    pub type DafnyString = String;

    use num::BigInt;

    use std::collections::HashMap;
    use std::collections::HashSet;
    use std::rc::Rc;
    use std::hash::Hash;

    pub fn dafny_int_to_bigint(i: &DafnyInt) -> BigInt {
        i.data.as_ref().clone()
    }
    pub fn bigint_to_dafny_int(i: &BigInt) -> DafnyInt {
        DafnyInt{data: Rc::new(i.clone())}
    }

    pub fn dafny_sequence_to_vec<T, X>(
        s: &DafnySequence<T>,
        elem_converter: fn(&T) -> X) -> Vec<X>
      where T: DafnyType
    {
        let mut array: Vec<T> = Vec::with_capacity(s.cardinality_usize());
        DafnySequence::<T>::append_recursive(&mut array, s);
        array.iter().map(|x| elem_converter(x)).collect()
    }

    // Used for external conversions
    pub fn vec_to_dafny_sequence<T, X>(array: &Vec<X>, elem_converter: fn(&X) -> T)
     -> DafnySequence<T>
      where T: DafnyType
    {
        let mut result: Vec<T> = Vec::with_capacity(array.len());
        for elem in array.iter() {
            result.push(elem_converter(elem));
        }
        DafnySequence::<T>::from_array_owned(result)
    }
    
    pub fn dafny_map_to_hashmap<K, V, K2, V2>(m: &DafnyMap<K, V>, converter_k: fn(&K)->K2, converter_v: fn(&V)->V2) -> HashMap<K2, V2>
      where
          K: DafnyTypeEq, V: DafnyTypeEq,
          K2: Eq + Hash, V2: Clone
    {
        m.to_hashmap_owned(converter_k, converter_v)
    }

    pub fn hashmap_to_dafny_map<K2, V2, K, V>(map: &HashMap<K2, V2>, converter_k: fn(&K2)->K, converter_v: fn(&V2)->V)
        -> DafnyMap<K, V>
      where
        K: DafnyTypeEq, V: DafnyTypeEq,
        K2: Eq + Hash, V2: Clone
    {
        DafnyMap::<K, V>::from_hashmap(map, converter_k, converter_v)
    }

    // --unicode-chars:true
    pub mod unicode_chars_true {
        use crate::Sequence;

        type DafnyString = Sequence<char>;

        pub fn string_to_dafny_string(s: &str) -> DafnyString {
            Sequence::from_array_owned(s.chars().collect())
        }
        pub fn dafny_string_to_string(s: &DafnyString) -> String {
            let characters = s.to_array();
            characters.iter().collect::<String>()
        }
    }
    
    // --unicode-chars:false
    pub mod unicode_chars_false {
        use crate::Sequence;

        type DafnyString = Sequence<u16>;

        pub fn string_to_dafny_string(s: &str) -> DafnyString {
            Sequence::from_array_owned(s.encode_utf16().collect())
        }
        pub fn dafny_string_to_string(s: &DafnyString) -> String {
            let characters = s.to_array();
            String::from_utf16_lossy(&characters)
        }
    }
    
    pub fn set_to_dafny_set<U, T: DafnyTypeEq>(set: &HashSet<U>, converter: fn(&U) -> T)
      -> DafnySet<T>
    {
        DafnySet::from_iterator(set.iter().map(converter))
    }
    pub fn dafny_set_to_set<T, U>(set: &DafnySet<T>, converter: fn(&T) -> U) -> HashSet<U>
        where T: DafnyTypeEq, U: Clone + Eq + Hash
    {
        let mut result: HashSet<U> = HashSet::new();
        for s in set.data.iter() {
            result.insert(converter(s));
        }
        result
    }

    pub fn dafny_multiset_to_owned_vec<T, U>(ms: &DafnyMultiset<T>, converter: fn(&T) -> U) -> Vec<U>
        where T: DafnyTypeEq, U: Clone + Eq
    {
        let mut result: Vec<U> = Vec::new();
        for s in ms.data.iter() {
            // Push T as many times as its size
            for _ in 0..*s.1 {
                result.push(converter(&s.0));
            }
        }
        result
    }

    pub fn vec_to_dafny_multiset<T, U>(vec: &Vec<U>, converter: fn(&U) -> T) -> DafnyMultiset<T>
        where T: DafnyTypeEq, U: Clone + Eq + Hash
    {
        DafnyMultiset::from_iterator(
            vec.into_iter().map(|u: &U| converter(u))
        )
    }

}


// **************
// Dafny integers
// **************

// Zero-cost abstraction over a Rc<BigInt>
pub struct DafnyInt {
    data: Rc<BigInt>
}

impl DafnyType for DafnyInt {}
impl DafnyTypeEq for DafnyInt {}

impl Clone for DafnyInt {
    fn clone(&self) -> Self {
        DafnyInt{data: Rc::clone(&self.data)}
    }
}

impl Default for DafnyInt {
    fn default() -> Self {
        DafnyInt{data: Rc::new(BigInt::zero())}
    }
}

impl PartialEq<DafnyInt> for DafnyInt {
    fn eq(&self, other: &DafnyInt) -> bool {
        self.data.eq(&other.data)
    }
}
impl Eq for DafnyInt {}
impl Hash for DafnyInt {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.data.hash(state);
    }
}

impl DafnyPrint for DafnyInt {
    fn fmt_print(&self, f: &mut Formatter<'_>, _in_seq: bool) -> std::fmt::Result {
        write!(f, "{}", self.data)
    }
}

impl Add<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn add(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt{data: Rc::new(self.data.as_ref() + rhs.data.as_ref())}
    }
}

impl Mul<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn mul(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt{data: Rc::new(self.data.as_ref() * rhs.data.as_ref())}
    }
}

impl Div<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn div(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt{data: Rc::new(self.data.as_ref() / rhs.data.as_ref())}
    }
}

impl Sub<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn sub(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt{data: Rc::new(self.data.as_ref() - rhs.data.as_ref())}
    }
}
impl Rem<DafnyInt> for DafnyInt {
    type Output = DafnyInt;

    fn rem(self, rhs: DafnyInt) -> Self::Output {
        DafnyInt{data: Rc::new(self.data.as_ref() % rhs.data.as_ref())}
    }
}
impl Neg for DafnyInt {
    type Output = DafnyInt;

    #[inline]
    fn neg(self) -> Self::Output {
        DafnyInt{data: Rc::new(-self.data.as_ref())}
    }
}
impl Zero for DafnyInt {
    #[inline]
    fn zero() -> Self {
        DafnyInt{data: Rc::new(BigInt::zero())}
    }
    #[inline]
    fn is_zero(&self) -> bool {
        self.data.is_zero()
    }
}
impl One for DafnyInt {
    #[inline]
    fn one() -> Self {
        DafnyInt{data: Rc::new(BigInt::one())}
    }
}
impl Num for DafnyInt {
    type FromStrRadixErr = ParseBigIntError;

    #[inline]
    fn from_str_radix(s: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Ok(DafnyInt{data: Rc::new(BigInt::from_str_radix(s, radix)?)})
    }
}
impl Ord for DafnyInt {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.data.cmp(&other.data)
    }
}
impl Signed for DafnyInt {
    #[inline]
    fn abs(&self) -> Self {
        DafnyInt{data: Rc::new(self.data.as_ref().abs())}
    }

    #[inline]
    fn abs_sub(&self, other: &Self) -> Self {
        DafnyInt{data: Rc::new(self.data.as_ref().abs_sub(other.data.as_ref()))}
    }

    #[inline]
    fn signum(&self) -> Self {
        DafnyInt{data: Rc::new(self.data.as_ref().signum())}
    }

    #[inline]
    fn is_positive(&self) -> bool {
        self.data.as_ref().is_positive()
    }

    #[inline]
    fn is_negative(&self) -> bool {
        self.data.as_ref().is_negative()
    }
}

// Comparison
impl PartialOrd<DafnyInt> for DafnyInt {
    #[inline]
    fn partial_cmp(&self, other: &DafnyInt) -> Option<Ordering> {
        self.data.partial_cmp(&other.data)
    }
}

impl DafnyInt {
    #[inline]
    pub fn parse_bytes(number: &[u8], radix: u32) -> DafnyInt {
        DafnyInt{data: ::std::rc::Rc::new(BigInt::parse_bytes(number, radix).unwrap())}
    }
    pub fn from_usize(usize: usize) -> DafnyInt {
        DafnyInt{data: Rc::new(BigInt::from(usize))}
    }
}

// **************
// Immutable sequences
// **************

impl <T: DafnyType> DafnyType for Sequence<T> {}
impl <T: DafnyTypeEq> DafnyTypeEq for Sequence<T> {}
impl <T: DafnyTypeEq> Eq for Sequence<T> {}

impl <T: DafnyType> Add<&Sequence<T>> for &Sequence<T>
{
    type Output = Sequence<T>;

    fn add(self, rhs: &Sequence<T>) -> Self::Output {
        Sequence::new_concat_sequence(self, rhs)
    }
}

impl <T: DafnyTypeEq> Hash for Sequence<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
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
  where T: DafnyType,
{
    ArraySequence {
        // Values could be a native array because we will know statically that all 
        // accesses are in bounds when using this data structure
        values: Rc<Vec<T>>,
    },
    ConcatSequence {
        left: Rc<UnsafeCell<Sequence<T>>>,
        right: Rc<UnsafeCell<Sequence<T>>>,
        length: SizeT,
        boxed: Rc<RefCell<Option<Rc<Vec<T>>>>>
    }
}

impl <T> Sequence<T>
where T: DafnyType {
    pub fn from_array_owned(values: Vec<T>) -> Sequence<T> {
        Sequence::ArraySequence {
            values: Rc::new(values),
        }
    }
    pub fn new_concat_sequence(left: &Sequence<T>, right: &Sequence<T>) -> Sequence<T> {
        Sequence::ConcatSequence {
            left: Rc::new(UnsafeCell::new(left.clone())),
            right: Rc::new(UnsafeCell::new(right.clone())),
            length: left.cardinality_usize() + right.cardinality_usize(),
            boxed: Rc::new(RefCell::new(None)),
        }
    }
    pub fn to_array(&self) -> Rc<Vec<T>> {
        // Let's convert the if then else below to a proper match statement
        match self {
            Sequence::ArraySequence { values, .. } =>
              // The length of the elements
              Rc::clone(values),
            Sequence::ConcatSequence { length, boxed, left, right } => {
                let clone_boxed = boxed.as_ref().clone();
                let clone_boxed_borrowed = clone_boxed.borrow();
                let borrowed: Option<&Rc<Vec<T>>> = clone_boxed_borrowed.as_ref();
                if let Some(cache) = borrowed.as_ref() {
                    return Rc::clone(cache);
                }
                // Let's create an array of size length and fill it up recursively
                // We don't materialize nested arrays because most of the time they are forgotten
                let mut array: Vec<T> = Vec::with_capacity(*length);
                Sequence::<T>::append_recursive(&mut array, self);
                let result = Rc::new(array);
                let mut cache = boxed.borrow_mut();
                let mutable_left: *mut Sequence<T> = left.get();
                let mutable_right: *mut Sequence<T> = right.get();
                unsafe { *mutable_left = Sequence::from_array_owned(vec!()) };
                unsafe { *mutable_right = Sequence::from_array_owned(vec!()) };
                *cache = Some(result.clone());
                result
            }
        }
    }

    pub fn append_recursive(array: &mut Vec<T>, this: &Sequence<T>) {
        match this {
            Sequence::ArraySequence { values, .. } =>
              // The length of the elements
              for value in values.iter() {
                array.push(value.clone());
              },
            Sequence::ConcatSequence { boxed, left, right, .. } =>
              // Let's create an array of size length and fill it up recursively
              {
                let clone_boxed = boxed.as_ref().clone();
                let clone_boxed_borrowed = clone_boxed.borrow();
                let borrowed: Option<&Rc<Vec<T>>> = clone_boxed_borrowed.as_ref();
                if let Some(values) = borrowed.as_ref() {
                    for value in values.iter() {
                        array.push(value.clone());
                    }
                    return;
                }
                Sequence::<T>::append_recursive(array, unsafe { &mut *left.get() });
                Sequence::<T>::append_recursive(array, unsafe { &mut *right.get() });
              }
        }
    }
    /// Returns the cardinality of this [`Sequence<T>`].
    // The cardinality returns the length of the sequence
    pub fn cardinality_usize(&self) -> SizeT {
        match self {
            Sequence::ArraySequence { values, .. } =>
              // The length of the elements
              values.len(),
            Sequence::ConcatSequence { length, .. } =>
              *length,
        }
    }
    pub fn cardinality(&self) -> DafnyInt {
        DafnyInt::from_usize(self.cardinality_usize())
    }
    pub fn select(&self, index: SizeT) -> T {
        let array = self.to_array();
        array[index].clone()
    }

    pub fn slice(&self, start: &DafnyInt, end: &DafnyInt) -> Sequence<T> {
        let start_index = start.data.as_ref().to_usize().unwrap();
        let end_index = end.data.as_ref().to_usize().unwrap();
        let new_data = Sequence::from_array_owned(self.to_array()[start_index..end_index].to_vec());
        new_data
    }
}

impl <T: DafnyTypeEq> Sequence<T> {
    pub fn contains(&self, value: &T) -> bool {
        self.to_array().contains(value)
    }
}
impl <T> PartialEq<Sequence<T>> for Sequence<T>
  where T: DafnyTypeEq
{
    fn eq(&self, other: &Sequence<T>) -> bool {
        // Iterate through both elements and verify that they are equal
        let values: Rc<Vec<T>> = self.to_array();
        let mut i: usize = 0;
        for value in values.iter() {
            if value != &other.select(i) {
                return false;
            }
            i += 1;
        }
        true
    }
}

impl <V: DafnyType> DafnyPrint for Sequence<V>
{
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
      f.write_str("[")?;
      let mut first = true;
      for value in self.to_array().iter() {
          if !first {
              f.write_str(", ")?;
          }
          first = false;
          value.fmt_print(f, in_seq)?;
      }
      f.write_str("]")
    }
}

// **************
// Immutable maps
// **************

#[derive(Clone)]
pub struct Map<K, V>
    where K: DafnyTypeEq, V: DafnyTypeEq
{
    data: Rc<HashMap<K, V>>
}

impl <K: DafnyTypeEq, V: DafnyTypeEq> Hash for Map<K, V>
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.data.len().hash(state); // Worst performance for things that are not hashable like maps
    }
}

impl <K, V> PartialEq<Map<K, V>> for Map<K, V>
  where K: DafnyTypeEq, V: DafnyTypeEq
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
        return true;
    }
}

impl <K: DafnyType, V: DafnyType> DafnyType for (K, V) {}
impl <K: DafnyTypeEq, V: DafnyTypeEq> DafnyTypeEq for (K, V) {}

impl <K: DafnyTypeEq, V: DafnyTypeEq> DafnyType for Map<K, V> {}
impl <K: DafnyTypeEq, V: DafnyTypeEq> DafnyTypeEq for Map<K, V> {}

impl <K: DafnyTypeEq, V: DafnyTypeEq> Eq for Map<K, V> {
}

impl <K: DafnyTypeEq, V: DafnyTypeEq> Map<K, V>
{
    pub fn new_empty() -> Map<K, V> {
        Map {
            data: Rc::new(HashMap::new())
        }
    }
    pub fn from_array_owned(values: Vec<(K, V)>) -> Map<K, V> {
        let mut result: HashMap<K, V> = HashMap::new();
        for (k, v) in values.iter() {
           result.insert(k.clone(), v.clone());
        }
        Self::from_hashmap_owned(result)
    }
    pub fn from_hashmap_owned(values: HashMap<K, V>) -> Map<K, V> {
        Map { data: Rc::new(values) }
    }
    pub fn to_hashmap_owned<K2, V2>(&self, converter_k: fn(&K)->K2, converter_v: fn(&V)->V2) -> HashMap<K2, V2>
      where K2: Eq + std::hash::Hash, V2: Clone
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
    pub fn add(&self, key: K, value: V) -> Map<K, V> {
        let mut data = self.data.as_ref().clone();
        data.insert(key, value);
        Map {
            data: Rc::new(data)
        }
    }
    pub fn merge(&self, other: &Map<K, V>) -> Map<K, V> {
        let mut new_data = (*other.data).clone();
        // Overriding self's keys with other's keys if there are some.
        for (k, v) in self.data.iter() {
            if !other.contains(k) {
                new_data.insert(k.clone(), v.clone());
            }
        }
        Map {
            data: Rc::new(new_data)
        }
    }
    pub fn subtract(&self, keys: &Set<K>) -> Self {
        let mut result: Vec<(K, V)> = Vec::new();
        for (k, v) in self.data.iter() {
            if !keys.contains(k) {
                result.push((k.clone(), v.clone()));
            }
        }
        Self::from_array_owned(result)
    }

    pub fn from_hashmap<K2, V2>(map: &HashMap<K2, V2>, converter_k: fn(&K2)->K, converter_v: fn(&V2)->V)
        -> Map<K, V>
      where
        K: DafnyTypeEq, V: DafnyTypeEq,
        K2: Eq + Hash, V2: Clone
    {
        let mut result: HashMap<K, V> = HashMap::new();
        for (k, v) in map.iter() {
            result.insert(converter_k(k), converter_v(v));
        }
        Map {
            data: Rc::new(result)
        }
    }
    pub fn keys(&self) -> Set<K> {
        let mut result: HashSet<K> = HashSet::new();
        for (k, _) in self.data.iter() {
            result.insert(k.clone());
        }
        Set::from_hashset_owned(result)
    }
    pub fn values(&self) -> Set<V> {
        let mut result: Vec<V> = Vec::new();
        for (_, v) in self.data.iter() {
            result.push(v.clone());
        }
        Set::from_array(&result)
    }
}


pub struct MapBuilder<K, V>
  where K: Clone + Eq + std::hash::Hash, V: Clone
{
    data: HashMap<K, V>
}

impl <K, V> MapBuilder<K, V>
  where K: DafnyTypeEq, V: DafnyTypeEq
{
    pub fn new() -> MapBuilder<K, V> {
        MapBuilder {
            data: HashMap::new()
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

impl <K, V> DafnyPrint for Map<K, V>
  where K: DafnyTypeEq, V: DafnyTypeEq
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
      f.write_str("}")
    
    }
}

// **************
// Immutable sets
// **************

#[derive(Clone)]
pub struct Set<V: DafnyTypeEq>
{
    data: Rc<HashSet<V>>
}

impl <V> PartialEq<Set<V>> for Set<V>
  where V: DafnyTypeEq
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

impl <V: DafnyTypeEq> Set<V> {
    pub fn new_empty() -> Set<V> {
        Self::from_hashset_owned(HashSet::new())
    }
    pub fn from_array(array: &Vec<V>) -> Set<V> {
        Self::from_iterator(array.iter().map(|v| v.clone()))
    }
    pub fn from_iterator<I>(data: I) -> Set<V>
      where I: Iterator<Item=V>
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
            data: Rc::new(hashset)
        }
    }
}

impl <V: DafnyTypeEq> Set<V>
{
    pub fn cardinality_usize(&self) -> usize {
        self.data.len()
    }
    pub fn cardinality(&self) -> DafnyInt {
        DafnyInt::from_usize(self.data.len())
    }
    pub fn contains(&self, value: &V) -> bool {
        self.data.contains(value)
    }
    pub fn merge(self: &Self, other: &Set<V>) -> Set<V> {
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

    pub fn intersect(self: &Self, other: &Set<V>) -> Set<V> {
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
            if !self.contains(value) {
                result.insert(value.clone());
            }
        }
        Set::from_hashset_owned(result)
    }

    pub fn is_disjoint_from(&self, other: &Set<V>) -> bool {
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

    pub fn is_subset_of(&self, other: &Set<V>) -> bool {
        if self.cardinality_usize() == 0 {
            return true;
        }
        if other.cardinality_usize() == 0 {
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
    
    pub fn is_proper_subset_of(&self, other: &Set<V>) -> bool {
        self.is_subset_of(other) && self.cardinality_usize() != other.cardinality_usize()
    }

    pub fn elements(self: &Self) -> Set<V> {
        self.clone()
    }
}

pub struct SetBuilder<T>
  where T: Clone + Eq + std::hash::Hash
{
    data: HashMap<T, bool>
}

impl <T: DafnyTypeEq> SetBuilder<T>
{
    pub fn new() -> SetBuilder<T> {
        SetBuilder {
            data: HashMap::new()
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

impl <V: DafnyTypeEq> DafnyPrint for Set<V>
{
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

// *******************
// Immutable multisets
// *******************

pub struct Multiset<V: DafnyTypeEq>
{
    data: HashMap<V, usize>
}

impl <V: DafnyTypeEq> Multiset<V>
{
    pub fn new_empty() -> Multiset<V> {
        Self::from_vec(&vec!())
    }
    pub fn from_map(map: &HashMap<V, usize>) -> Multiset<V>{
        Multiset {
            data: map.clone()
        }
    }
    pub fn from_vec(data: &Vec<V>) -> Multiset<V> {
        Self::from_iterator(data.iter().map(|x| x.clone()))
    }
    pub fn from_iterator<I>(data: I) -> Multiset<V>
      where I: Iterator<Item=V>
    {
        let mut hashmap: HashMap<V, usize> = HashMap::new();
        for value in data {
            let count = hashmap.entry(value.clone()).or_insert(0);
            *count += 1;
        }
        Multiset {
            data: hashmap
        }
    }
    pub fn from_set(set: &Set<V>) -> Multiset<V> {
        Self::from_iterator(set.data.iter().map(|v| v.clone()))
    }
}

trait MultisetInterface<V>
  where V: DafnyTypeEq
{
    fn cardinality(&self) -> SizeT;
    fn cardinality_int(&self) -> Rc<BigInt>;
    fn contains(&self, value: &V) -> bool;
    fn update_count(&self, value: &V, new_count: &usize) -> Multiset<V>;
    fn union(&self, other: &Multiset<V>) -> Multiset<V>;
    fn intersection(&self, other: &Multiset<V>) -> Multiset<V>;
    fn subtract(&self, other: &Multiset<V>) -> Multiset<V>;
    fn is_disjoint_from(&self, other: &Multiset<V>) -> bool;
    fn equals(&self, other: &Multiset<V>) -> bool;
    fn is_subset_of(&self, other: &Multiset<V>) -> bool;
    fn is_proper_subset_of(&self, other: &Multiset<V>) -> bool;
}

// Generic function to allocate and return a raw pointer immediately
#[inline]
pub fn allocate<T: ?Sized>(value: Box<T>) -> *const T {
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
// Define the AsAny trait
pub trait AsAny {
  fn as_any(&self) -> &dyn Any;
}
pub fn is_instance_of<C: ?Sized + AsAny, U: 'static>(theobject: *const C) -> bool {
    unsafe { &*theobject }.as_any().downcast_ref::<U>().is_some()
}
trait DafnyUpdowncast<U: ?Sized> {
    fn updowncast(&self) -> U;
    fn is_instance_of(&self) -> bool;
}
/*impl <T: ?Sized + AsAny, U: 'static> DafnyUpdowncast<*const U> for T
{
    fn updowncast(&self) -> *const U {
        self.as_any().downcast_ref::<U>().unwrap()
    }

    fn is_instance_of(&self) -> bool {
        is_instance_of::<T, U>(self)
        //self.as_any().downcast_ref::<U>().is_some()
    }
}*/
impl <T: ?Sized + AsAny, U: 'static> DafnyUpdowncast<*const U> for *const T
{
    fn updowncast(&self) -> *const U {
        unsafe { &**self }.as_any().downcast_ref::<U>().unwrap()
    }

    fn is_instance_of(&self) -> bool {
        is_instance_of::<T, U>(*self)
        //self.as_any().downcast_ref::<U>().is_some()
    }
}
impl <T: ?Sized + AsAny, U: 'static> DafnyUpdowncast<*const U> for Rc<T>
{
    fn updowncast(&self) -> *const U {
        self.as_any().downcast_ref::<U>().unwrap()
    }

    fn is_instance_of(&self) -> bool {
        is_instance_of::<T, U>(self.as_ref())
        //self.as_any().downcast_ref::<U>().is_some()
    }
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

// from gazebo
#[inline]
pub unsafe fn transmute_unchecked<A, B>(x: A) -> B {
    assert_eq!(std::mem::size_of::<A>(), std::mem::size_of::<B>());
    debug_assert_eq!(0, (&x as *const A).align_offset(std::mem::align_of::<B>()));
    let b = std::ptr::read(&x as *const A as *const B);
    std::mem::forget(x);
    b
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
        impl DafnyType for $name {}
        impl DafnyTypeEq for $name {}
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

impl DafnyType for char {}
impl DafnyTypeEq for char {}

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

pub fn char_lt(left: char, right: char) -> bool {
    let left_code = left as u32;
    let right_code = right as u32;

    left_code < right_code
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

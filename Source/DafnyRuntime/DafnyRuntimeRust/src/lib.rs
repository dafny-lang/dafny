#[cfg(test)]
mod tests;
use std::{any::Any, borrow::Borrow, cell::RefCell, cmp::Ordering, collections::{HashMap, HashSet}, fmt::{Display, Formatter}, hash::Hash, ops::{Add, Deref, Div, Index, Mul, Neg, Rem, Sub}, rc::Rc};
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
    pub type DafnyInt = crate::DafnyInt;
    pub type DafnySequence<T> = crate::DafnySequence<T>;
    pub type DafnyMap<K, V> = Rc<Map<K, V>>;
    pub type DafnySet<T> = Rc<Set<T>>;
    pub type DafnyMultiset<T> = Rc<Multiset<T>>;
    pub type DafnyBool = bool;
    pub type DafnyString = String;

    use num::BigInt;

    use crate::Sequence;
    use crate::Map;
    use crate::Set;
    use crate::Multiset;
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
      where T: Clone
    {
        let mut array: Vec<T> = Vec::with_capacity(s.cardinality_usize());
        Sequence::<T>::append_recursive(&mut array, s.data.as_ref());
        array.iter().map(|x| elem_converter(x)).collect()
    }

    // Used for external conversions
    pub fn vec_to_dafny_sequence<T, X>(array: &Vec<X>, elem_converter: fn(&X) -> T)
     -> DafnySequence<T>
      where T: Clone
    {
        let mut result: Vec<T> = Vec::with_capacity(array.len());
        for elem in array.iter() {
            result.push(elem_converter(elem));
        }
        DafnySequence {data: Sequence::<T>::from_array_owned(result) }
    }
    
    pub fn dafny_map_to_hashmap<K, V, K2, V2>(m: &DafnyMap<K, V>, converter_k: fn(&K)->K2, converter_v: fn(&V)->V2) -> HashMap<K2, V2>
      where
          K: Eq + Clone + Hash + super::DafnyPrint, V: Clone + Eq,
          K2: Eq + Hash, V2: Clone
    {
        m.to_hashmap_owned(converter_k, converter_v)
    }

    pub fn hashmap_to_dafny_map<K2, V2, K, V>(map: &HashMap<K2, V2>, converter_k: fn(&K2)->K, converter_v: fn(&V2)->V)
        -> DafnyMap<K, V>
      where
        K: Eq + Clone + Hash + super::DafnyPrint, V: Clone + Eq,
        K2: Eq + Hash, V2: Clone
    {
        Map::<K, V>::from_hashmap(map, converter_k, converter_v)
    }

    // --unicode-chars:true
    pub mod unicode_chars_true {
        use crate::DafnySequence;

        type DafnyString = DafnySequence<char>;

        pub fn string_to_dafny_string(s: &str) -> DafnyString {
            DafnySequence::from_array_owned(s.chars().collect())
        }
        pub fn dafny_string_to_string(s: &DafnyString) -> String {
            let characters = s.data.to_array();
            characters.iter().collect::<String>()
        }
    }
    
    // --unicode-chars:false
    pub mod unicode_chars_false {
        use crate::DafnySequence;

        type DafnyString = DafnySequence<u16>;

        pub fn string_to_dafny_string(s: &str) -> DafnyString {
            DafnySequence::from_array_owned(s.encode_utf16().collect())
        }
        pub fn dafny_string_to_string(s: &DafnyString) -> String {
            let characters = s.data.as_ref().to_array();
            String::from_utf16_lossy(&characters)
        }
    }
    
    pub fn set_to_dafny_set<T, U>(set: &HashSet<T>, converter: fn(&T) -> U)
      -> DafnySet<U>
        where T: Clone + Eq + Hash, U: Clone + Eq
    {
        let mut result: Vec<U> = Vec::new();
        for s in set.iter() {
            result.push(converter(s));
        }
        Set::from_array_owned_unique(result)
    }
    pub fn dafny_set_to_set<T, U>(set: &DafnySet<T>, converter: fn(&T) -> U) -> HashSet<U>
        where T: Clone + Eq, U: Clone + Eq + Hash
    {
        let mut result: HashSet<U> = HashSet::new();
        for s in set.data.to_array().iter() {
            result.insert(converter(s));
        }
        result
    }

    pub fn dafny_multiset_to_owned_vec<T, U>(ms: &DafnyMultiset<T>, converter: fn(&T) -> U) -> Vec<U>
        where T: Clone + Eq + Hash, U: Clone + Eq
    {
        let mut result: Vec<U> = Vec::new();
        for s in ms.data.data.to_array().iter() {
            // Push T as many times as its size
            for _ in 0..s.1 {
                result.push(converter(&s.0));
            }
        }
        result
    }

    pub fn vec_to_dafny_multiset<T, U>(vec: &Vec<U>, converter: fn(&U) -> T) -> DafnyMultiset<T>
        where T: Clone + Eq + Hash + super::DafnyPrint, U: Clone + Eq + Hash
    {
        Multiset::from_array_owned(
            vec.into_iter().map(|u: &U| converter(u)).collect()
        )
    }

}

// Zero-cost abstraction over a Rc<BigInt>
pub struct DafnyInt {
    data: Rc<BigInt>
}

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
}

pub struct DafnySequence<T>
  where T: Clone
{
    data: Rc<Sequence<T>>
}

// Inlined wrappers around Rc<Sequence<T>>
impl <T: Clone> DafnySequence<T> {
    #[inline]
    pub fn cardinality(&self) -> DafnyInt {
        self.data.cardinality()
    }
    #[inline]
    pub fn cardinality_usize(&self) -> usize {
        self.data.cardinality_usize()
    }
    #[inline]
    pub fn from_array_owned(values: Vec<T>) -> DafnySequence<T> {
        DafnySequence{data: Sequence::from_array_owned(values)}
    }
    #[inline]
    pub fn concat(&self, other: &DafnySequence<T>) -> DafnySequence<T> {
        DafnySequence{data: 
            Sequence::new_lazy_sequence(
            &Sequence::new_concat_sequence(&self.data, &other.data))}
    }
    #[inline]
    pub fn slice(&self, start: &DafnyInt, end: &DafnyInt) -> DafnySequence<T> {
        DafnySequence{data: Sequence::slice(&self.data, start, end)}
    }
}

impl <T> Add<&DafnySequence<T>> for &DafnySequence<T>
  where T: Clone
{
    type Output = DafnySequence<T>;

    fn add(self, rhs: &DafnySequence<T>) -> Self::Output {
        self.concat(rhs)
    }
}

impl <T> Index<&DafnyInt> for DafnySequence<T>
  where T: Clone
{
    type Output = T;

    fn index(&self, index: &DafnyInt) -> &T {
        self.data.select_borrow(index.data.as_ref().to_usize().unwrap())
    }
}

pub enum Sequence<T>
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

impl <T> Sequence<T>
where T: Clone {
    pub fn from_array_owned(values: Vec<T>) -> Rc<Sequence<T>> {
        Rc::new(Sequence::ArraySequence {
            values: Rc::new(values),
        })
    }
    pub fn new_concat_sequence(left: &Rc<Sequence<T>>, right: &Rc<Sequence<T>>) -> Rc<Sequence<T>> {
        Rc::new(Sequence::ConcatSequence {
            left: Rc::clone(&left),
            right: Rc::clone(&right),
            length: left.cardinality_usize() + right.cardinality_usize(),
        })
    }
    pub fn new_lazy_sequence(underlying: &Rc<Sequence<T>>) -> Rc<Sequence<T>> {
        Rc::new(Sequence::LazySequence {
            length: underlying.cardinality_usize(),
            boxed: RefCell::new(Rc::clone(underlying)),
        })
    }
    pub fn to_array(&self) -> Rc<Vec<T>> {
        // Let's convert the if then else below to a proper match statement
        match self {
            Sequence::ArraySequence { values, .. } =>
              // The length of the elements
              Rc::clone(values),
            Sequence::ConcatSequence { length, .. } => {
              // Let's create an array of size length and fill it up recursively
                let mut array: Vec<T> = Vec::with_capacity(*length);
                Sequence::<T>::append_recursive(&mut array, self);
                Rc::new(array)
            },
            Sequence::LazySequence { boxed,.. } => {
                let result: Rc<Vec<T>> = boxed.borrow().to_array();
                // Put the value back into boxed
                boxed.replace(Rc::new(
                    Sequence::<T>::ArraySequence{values: result.clone()}));
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
    pub fn cardinality_usize(&self) -> SizeT {
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
    pub fn cardinality(&self) -> DafnyInt {
        DafnyInt{data: Rc::new(BigInt::from_usize(self.cardinality_usize()).unwrap())}
    }
    pub fn select(&self, index: SizeT) -> T {
        let array = self.to_array();
        array[index].clone()
    }
    pub fn select_borrow<'a>(&'a self, index: SizeT) -> &'a T {
        match self {
            Sequence::ArraySequence { values, .. } =>
                &values[index],
              
            Sequence::ConcatSequence { .. } => {
              panic!("ConcatSequence should have been wrapped in a LazySequence")
            },
            Sequence::LazySequence { boxed, .. } => {
                let result = boxed.borrow().to_array();
                // Put the value back into boxed
                boxed.replace(Rc::new(
                    Sequence::<T>::ArraySequence{values: result}));
                unsafe{ std::mem::transmute::<&Sequence<T>, &'a Sequence<T>>( boxed.borrow().as_ref())}.select_borrow(index)
            }
        }
    }

    pub fn slice(&self, start: &DafnyInt, end: &DafnyInt) -> Rc<Sequence<T>> {
        let start_index = start.data.as_ref().to_usize().unwrap();
        let end_index = end.data.as_ref().to_usize().unwrap();
        let new_data = Sequence::from_array_owned(self.to_array()[start_index..end_index].to_vec());
        new_data
    }
}

impl <T> Sequence<T> where T: Eq + Clone {
    pub fn contains(&self, value: &T) -> bool {
        self.to_array().contains(value)
    }
}
impl <T, U> PartialEq<Sequence<U>> for Sequence<T>
  where T: Clone + PartialEq<U>,
        U: Clone
  {
    fn eq(&self, other: &Sequence<U>) -> bool {
        // Iterate through both elements and verify that they are equal
        let values = self.to_array();
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

impl <V> DafnyPrint for Sequence<V>
  where V: DafnyPrint + Clone
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

// TODO: Find how to not depend on Hash, by default
pub struct Map<K, V> 
  where K: Clone + Eq + std::hash::Hash, V: Clone
{
    data: Rc<Sequence<(K, V)>>,
    // Any time we explicitly access this map, we index the data
    cache: RefCell<Option<HashMap<K, V>>>
}

impl <K, V> PartialEq<Map<K, V>> for Map<K, V>
  where K: Clone + Eq + Hash + DafnyPrint, V: Clone + Eq
{
    fn eq(&self, other: &Map<K, V>) -> bool {
        // 1. Same cardinality
        // 2. All the elements of self are in the other
        if self.cardinality_usize() != other.cardinality_usize() {
            false
        } else {
            for (k, v) in self.data.to_array().iter() {
                // Use get_or_none on other. If the result is none, then return false
                // If the result is different, return false
                if other.get_or_none(k) != Some(v.clone()) {
                    return false;
                }
            }
            true
        }
    }
}

impl <K, V> Map<K, V>
  where K: Clone + Eq + std::hash::Hash + DafnyPrint, V: Clone + Eq
{
    pub fn new_empty() -> Rc<Map<K, V>> {
        Rc::new(Map {
            data: Sequence::from_array_owned(Vec::new()),
            cache: RefCell::new(None)
        })
    }
    pub fn from_array_owned_unique(values: Vec<(K, V)>) -> Rc<Map<K, V>> {
        Self::new_from_sequence(&Sequence::<(K, V)>::from_array_owned(values))
    }
    pub fn from_array_owned(values: Vec<(K, V)>) -> Rc<Map<K, V>> {
        let mut values = values;
        // Need to remove duplicates from the right to the left
        for i in (0..values.len()).rev() {
            for j in 0..i {
                if values[j].0 == values[i].0 {
                    values.remove(i);
                    break;
                }
            }
        }
        Self::from_array_owned_unique(values)
    }
    pub fn new_from_sequence(data: &Rc<Sequence<(K, V)>>) -> Rc<Map<K, V>> {
        Rc::new(Map {
            data: Rc::clone(data),
            cache: RefCell::new(None)
        })
    }
    pub fn to_hashmap_owned<K2, V2>(&self, converter_k: fn(&K)->K2, converter_v: fn(&V)->V2) -> HashMap<K2, V2>
      where K2: Eq + std::hash::Hash, V2: Clone
    {
        let mut result: HashMap<K2, V2> = HashMap::new();
        for (k, v) in self.data.to_array().iter() {
            result.insert(converter_k(k), converter_v(v));
        }
        result
    }
    pub fn compute_hashmap(&self) {
        let mut cache = self.cache.borrow_mut();
        if cache.is_none() {
            *cache = Some(self.to_hashmap_owned(
                |x| x.clone(),
                |x| x.clone()
            ));
        }
    }
    pub fn cardinality_usize(&self) -> usize {
        self.data.cardinality_usize()
    }
    pub fn cardinality(&self) -> DafnyInt {
        self.data.cardinality()
    }
    pub fn contains(&self, key: &K) -> bool {
        self.compute_hashmap();
        self.cache.borrow_mut().as_ref().unwrap().contains_key(key)
    }
    pub fn get_or_none(&self, key: &K) -> Option<V> {
        self.compute_hashmap();
        self.cache.borrow_mut().as_ref().unwrap().get(key).map(|v: &V| v.clone())
    }
    // Dafny will normally guarantee that the key exists.
    pub fn get(&self, key: &K) -> V {
        self.compute_hashmap();
        self.cache.borrow_mut().as_ref().unwrap().get(key).unwrap().clone()
    }
    pub fn add(&self, key: K, value: V) -> Rc<Map<K, V>> {
        let new_data = Sequence::<(K, V)>::from_array_owned(
            vec![(key, value)]);
        let combined_data = Sequence::<(K, V)>::new_concat_sequence(
            &self.data, &new_data);
        Rc::new(Map {
            data: combined_data,
            cache: RefCell::new(None)
        })
    }
    pub fn add_multiple(&self, other: &Rc<Map<K, V>>) -> Rc<Map<K, V>> {
        let new_data = Rc::clone(&other.data);
        let combined_data = Sequence::<(K, V)>::new_concat_sequence(
            &self.data, &new_data);
        Rc::new(Map {
            data: combined_data,
            cache: RefCell::new(None)
        })
    }
    pub fn substract(self : &Rc<Self>, keys: &Rc<Set<K>>) -> Rc<Self> {
        let mut result: Vec<(K, V)> = Vec::new();
        for (k, v) in self.data.to_array().iter() {
            if !keys.contains(k) {
                result.push((k.clone(), v.clone()));
            }
        }
        Self::from_array_owned(result)
    }

    pub fn from_hashmap<K2, V2>(map: &HashMap<K2, V2>, converter_k: fn(&K2)->K, converter_v: fn(&V2)->V)
        -> Rc<Map<K, V>>
      where
        K: Eq + Clone + Hash, V: Clone,
        K2: Eq + Hash, V2: Clone
    {
        let mut result: Vec<(K, V)> = Vec::new();
        for (k, v) in map.iter() {
            result.push((converter_k(k), converter_v(v)));
        }
        let s = Sequence::<(K, V)>::from_array_owned(result);
        Rc::new(Map {
            data: s,
            cache: RefCell::new(None)
        })
    }
    pub fn keys(&self) -> Rc<Set<K>> {
        let mut result: Vec<K> = Vec::new();
        for (k, _) in self.data.to_array().iter() {
            result.push(k.clone());
        }
        Set::from_array_owned_unique(result)
    }
    pub fn values(&self) -> Rc<Set<V>> {
        let mut result: Vec<V> = Vec::new();
        for (_, v) in self.data.to_array().iter() {
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
  where K: Clone + Eq + std::hash::Hash + DafnyPrint, V: Clone + Eq
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
    pub fn build(&self) -> Rc<Map<K, V>> {
        // Iterate over all the key values of the hashmap and add them to an array
        let mut result: Vec<(K, V)> = Vec::new();
        for (k, v) in self.data.iter() {
            result.push((k.clone(), v.clone()));
        }
        
        Map::from_array_owned(result)
    }
}

impl <K, V> DafnyPrint for Map<K, V>
  where K: DafnyPrint + Clone + Eq + Hash, V: DafnyPrint + Clone
{
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        f.write_str("map[")?;
      let mut first = true;
      for (k, v) in self.data.to_array().iter() {
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

pub struct Set<V>
  where V: Clone + Eq
{
    data: Rc<Sequence<V>>
    // Should we add a cache for faster lookup? But it requires Hash trait.
}

// Implement equality for sets
// TODO: Specialize if V implements Hashset
impl <V> PartialEq<Set<V>> for Set<V>
  where V: Clone + Eq + DafnyPrint
{
    fn eq(&self, other: &Set<V>) -> bool {
        // 1. Same cardinality
        // 2. All the elements of self are in the other
        if self.cardinality_usize() != other.cardinality_usize() {
            false
        } else {
            for value in self.data.to_array().iter() {
                if !other.contains(value) {
                    return false;
                }
            }
            for value in other.data.to_array().iter() {
                if !self.contains(value) {
                    return false;
                }
            }
            true
        }
    }
}

impl <V> Set<V> where V: Clone + Eq {
    pub fn new_empty() -> Rc<Set<V>> {
        Self::from_array_owned_unique(Vec::new())
    }
    pub fn from_array(array: &Vec<V>) -> Rc<Set<V>> {
        let mut unique_array: Vec<V> = Vec::new();
        for value in array.iter() {
            if !unique_array.contains(value) {
                unique_array.push(value.clone());
            }
        }
        Self::from_array_owned_unique(unique_array)
    }
    pub fn from_sequence(data: &Rc<Sequence<V>>) -> Rc<Set<V>> {
        Self::from_array(data.to_array().borrow())
    }
    pub fn from_array_owned_unique(unique_array: Vec<V>) -> Rc<Set<V>> {
        Rc::new(Set {
            data: Sequence::from_array_owned(unique_array)
        })
    }
}

impl <V> Set<V>
  where V: Clone + Eq + DafnyPrint
{
    pub fn cardinality_usize(&self) -> usize {
        self.data.cardinality_usize()
    }
    pub fn cardinality(&self) -> DafnyInt {
        self.data.cardinality()
    }
    pub fn contains(&self, value: &V) -> bool {
        self.data.contains(value)
    }
    pub fn union(self: &Rc<Self>, other: &Rc<Set<V>>) -> Rc<Set<V>> {
        if self.cardinality_usize() == 0 {
            return Rc::clone(other);
        }
        if other.cardinality_usize() == 0 {
            return Rc::clone(self);
        }
        let mut result = Rc::clone(&self.data);
        // iterate over the other, add only not contained elements
        for value in other.data.to_array().iter() {
            if !result.contains(value) {
                result = Sequence::<V>::new_concat_sequence(&result,
                     &Sequence::from_array_owned(vec![value.clone()]));
            }
        }
        let result_lazy = Sequence::<V>::new_lazy_sequence(&result);
        Set::from_sequence(&result_lazy)
    }

    pub fn intersection(self: &Rc<Self>, other: &Rc<Set<V>>) -> Rc<Set<V>> {
        if self.cardinality_usize() == 0 {
            return Rc::clone(self);
        }
        if other.cardinality_usize() == 0 {
            return Rc::clone(other);
        }
        // Start with an empty vec with capacity the smallest of both sets
        let mut result =
            Vec::with_capacity(
                std::cmp::min(self.cardinality_usize(), other.cardinality_usize()));
          
        // iterate over the other, take only elements in common
        for value in other.data.to_array().iter() {
            if self.contains(value) {
                result.push(value.clone());
            }
        }
        Set::from_array(&Rc::new(result))
    }

    pub fn difference(self: &Rc<Self>, other: &Rc<Set<V>>) -> Rc<Set<V>> {
        if self.cardinality_usize() == 0 {
            return Rc::clone(self);
        }
        if other.cardinality_usize() == 0 {
            return Rc::clone(self);
        }
        // Start with a vec the size of the first one
        let mut result =
            Vec::with_capacity(self.cardinality_usize());
          
        // iterate over the other, take only elements not in second
        for value in other.data.to_array().iter() {
            if !self.contains(value) {
                result.push(value.clone());
            }
        }
        Set::from_array(&Rc::new(result))
    }

    pub fn is_disjoint_from(&self, other: &Rc<Set<V>>) -> bool {
        if self.cardinality_usize() == 0 {
            return true;
        }
        if other.cardinality_usize() == 0 {
            return true;
        }
        // iterate over the other, take only elements not in second
        for value in other.data.to_array().iter() {
            if self.contains(value) {
                return false;
            }
        }
        true
    }

    pub fn equals(&self, other: &Rc<Set<V>>) -> bool {
        if self.cardinality_usize() != other.cardinality_usize() {
            return false;
        }
        // iterate over the other, take only elements not in second
        for value in other.data.to_array().iter() {
            if !self.contains(value) {
                return false;
            }
        }
        true
    }

    pub fn is_subset_of(&self, other: &Rc<Set<V>>) -> bool {
        if self.cardinality_usize() == 0 {
            return true;
        }
        if other.cardinality_usize() == 0 {
            return false;
        }
        // iterate over the other, take only elements not in second
        for value in other.data.to_array().iter() {
            if !self.contains(value) {
                return false;
            }
        }
        true
    }
    
    pub fn is_proper_subset_of(&self, other: &Rc<Set<V>>) -> bool {
        self.is_subset_of(other) && self.cardinality_usize() != other.cardinality_usize()
    }

    pub fn elements(self: &Rc<Self>) -> Rc<Set<V>> {
        Rc::clone(self)
    }
}

pub struct SetBuilder<T>
  where T: Clone + Eq + std::hash::Hash
{
    data: HashMap<T, bool>
}

impl <T> SetBuilder<T>
  where T: Clone + Eq + std::hash::Hash
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
    pub fn build(self) -> Rc<Set<T>> {
        // Iterate over all the key values of the hashmap and add them to an array
        let mut result: Vec<T> = Vec::new();
        for (k, _v) in self.data.iter() {
            result.push(k.clone());
        }
        
        Set::from_array(&result)
    }
}

impl <V> DafnyPrint for Set<V>
  where V: Clone + Eq + DafnyPrint
{
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        f.write_str("{")?;
        let mut first = true;
        for value in self.data.to_array().iter() {
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

pub struct Multiset<V>
  where V: Clone + Eq + Hash
{
    data: Rc<Map<V, usize>>
}

// Implement equality for sets
/*impl <V> DafnyImmutableEq<Rc<Multiset<V>>> for Rc<Multiset<V>>
  where V: Clone + Eq + DafnyPrint + Hash
{
    fn eq(&self, other: &Rc<Multiset<V>>) -> bool {
        Multiset::<V>::difference(self, other).cardinality() == 0
        && Multiset::<V>::difference(other, self).cardinality() == 0
    }
}*/

impl <V> Multiset<V>
  where V: Clone + Eq + Hash + DafnyPrint
{
    pub fn new_empty() -> Rc<Multiset<V>> {
        Self::from_map(&Map::new_empty())
    }
    pub fn from_map(data: &Rc<Map<V, usize>>) -> Rc<Multiset<V>>{
        Rc::new(Multiset {
            data: data.clone()
        })
    }
    pub fn from_array_owned(data: Vec<V>) -> Rc<Multiset<V>> {
        // Create an ArraySequence from the data
        let seq = Sequence::<V>::from_array_owned(data);
        // Create a Map from the ArraySequence
        Self::from_seq(&seq)
    }
    pub fn from_seq(data: &Rc<Sequence<V>>) -> Rc<Multiset<V>> {
        let mut hashmap: HashMap<V, usize> = HashMap::new();
        for value in data.to_array().iter() {
            let count = hashmap.entry(value.clone()).or_insert(0);
            *count += 1;
        }
        let map = Map::<V, usize>::from_hashmap(
            &hashmap, |v| v.clone(), 
            |u| u.clone());
        Self::from_map(&map)
    }
    pub fn from_set(set: &Rc<Set<V>>) -> Rc<Multiset<V>> {
        let seq = &set.data;
        Self::from_seq(seq)
    }
}

trait MultisetInterface<V>
  where V: Clone + Eq + Hash
{
    fn cardinality(&self) -> SizeT;
    fn cardinality_int(&self) -> Rc<BigInt>;
    fn contains(&self, value: &V) -> bool;
    fn update_count(&self, value: &V, new_count: &usize) -> Rc<Multiset<V>>;
    fn union(&self, other: &Rc<Multiset<V>>) -> Rc<Multiset<V>>;
    fn intersection(&self, other: &Rc<Multiset<V>>) -> Rc<Multiset<V>>;
    fn difference(&self, other: &Rc<Multiset<V>>) -> Rc<Multiset<V>>;
    fn is_disjoint_from(&self, other: &Rc<Multiset<V>>) -> bool;
    fn equals(&self, other: &Rc<Multiset<V>>) -> bool;
    fn is_subset_of(&self, other: &Rc<Multiset<V>>) -> bool;
    fn is_proper_subset_of(&self, other: &Rc<Multiset<V>>) -> bool;
}

// Rust Clinic: Can we have different implementations if V does not support Hash? 
/*impl <V> MultisetInterface for Rc<Multiset<V>>
  where V: Clone + Eq + Hash
{
    pub fn cardinality(&self) -> SizeT {
        // The cardinality of a multiset is the sum of the counts of each element
        let mut sum = 0;
        for (_, count) in self.data.iter() {
            sum += count;
        }
        sum
    }
    pub fn cardinality_int(&self) -> Rc<BigInt> {
        Rc::new(BigInt::from(self.cardinality() as i64))
    }
    pub fn contains(&self, value: &V) -> bool {
        self.data.contains_key(value)
    }
    // update_count returns the original multiset if the count is unchanged.
    //fn update_count(&self, value: &V, new_count: &usize) -> Rc<Multiset<V>> {
    //}
}*/

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

impl <T: DafnyPrint + Clone> DafnyPrint for DafnySequence<T> {
    fn fmt_print(&self, f: &mut Formatter<'_>, in_seq: bool) -> std::fmt::Result {
        let result = self.data.to_array();
        result.fmt_print(f, in_seq)
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

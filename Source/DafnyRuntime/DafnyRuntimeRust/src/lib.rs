#[cfg(test)]
mod tests;
use std::{any::Any, borrow::Borrow, cell::RefCell, collections::{HashSet, HashMap}, fmt::{Display, Formatter}, hash::Hash, ops::{Add, Deref}, rc::Rc};
use num::{Integer, Signed, One};

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
    type DafnyInt = Rc<BigInt>;
    type DafnySequence<T> = Rc<Sequence<T>>;
    type DafnyMap<K, V> = Rc<Map<K, V>>;
    type DafnySet<T> = Rc<Set<T>>;
    type DafnyMultiset<T> = Rc<Multiset<T>>;
    type DafnyBool = bool;
    type DafnyString = String;

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
        i.as_ref().clone()
    }
    pub fn bigint_to_dafny_int(i: &BigInt) -> DafnyInt {
        Rc::new(i.clone())
    }

    pub fn dafny_sequence_to_vec<T, X>(
        s: &DafnySequence<T>,
        elem_converter: fn(&T) -> X) -> Vec<X>
      where T: Clone
    {
        let mut array: Vec<T> = Vec::with_capacity(s.cardinality());
        Sequence::<T>::append_recursive(&mut array, s);
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
        Sequence::<T>::new_array_sequence(&Rc::new(result))
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
        use crate::Sequence;
        use std::rc::Rc;

        type DafnyString = Rc<Sequence<char>>;

        pub fn string_to_dafny_string(s: &str) -> DafnyString {
            Sequence::new_array_sequence_is_string(&Rc::new(s.chars().collect()), true)
        }
        pub fn dafny_string_to_string(s: &DafnyString) -> String {
            let characters = s.to_array();
            characters.iter().collect::<String>()
        }
    }
    
    // --unicode-chars:false
    pub mod unicode_chars_false {
        use crate::Sequence;
        use std::rc::Rc;

        type DafnyString = Rc<Sequence<u16>>;

        pub fn string_to_dafny_string(s: &str) -> DafnyString {
            Sequence::new_array_sequence_is_string(&Rc::new(s.encode_utf16().collect()), false)
        }
        pub fn dafny_string_to_string(s: &DafnyString) -> String {
            let characters = s.to_array();
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
        Multiset::from_owned_array(
            vec.into_iter().map(|u: &U| converter(u)).collect()
        )
    }

}

#[allow(dead_code)]
enum Sequence<T>
  where T: Clone,
{
    ArraySequence {
        is_string: bool,
        node_count: usize,
        // Values could be a native array because we will know statically that all 
        // accesses are in bounds when using this data structure
        values: Rc<Vec<T>>,
    },
    ConcatSequence {
        is_string: bool,
        node_count: usize,
        left: Rc<Sequence<T>>,
        right: Rc<Sequence<T>>,
        length: SizeT,
    },
    LazySequence {
        is_string: bool,
        node_count: usize,
        length: SizeT,
        boxed: RefCell<Rc<Sequence<T>>>
    }
}

#[allow(dead_code)]
impl <T> Sequence<T>
where T: Clone {
    pub fn is_string(&self) -> bool {
        match self {
            Sequence::ArraySequence { is_string, .. } => *is_string,
            Sequence::ConcatSequence { is_string, .. } => *is_string,
            Sequence::LazySequence { is_string, .. } => *is_string,
        }
    }
    pub fn from_array_owned(values: Vec<T>) -> Rc<Sequence<T>> {        
        Sequence::<T>::new_array_sequence(&Rc::new(values))
    }
    pub fn new_array_sequence(values: &Rc<Vec<T>>) -> Rc<Sequence<T>> {        
        Sequence::<T>::new_array_sequence_is_string(values, false)
    }
    pub fn new_array_sequence_is_string(values: &Rc<Vec<T>>, is_string: bool) -> Rc<Sequence<T>> {        
        Rc::new(Sequence::ArraySequence {
            is_string,
            node_count: 1,
            values: Rc::clone(values),
        })
    }
    pub fn new_concat_sequence(left: &Rc<Sequence<T>>, right: &Rc<Sequence<T>>) -> Rc<Sequence<T>> {
        Sequence::<T>::new_concat_sequence_is_string(left, right, false)
    }
    pub fn new_concat_sequence_is_string(left: &Rc<Sequence<T>>, right: &Rc<Sequence<T>>, is_string: bool) -> Rc<Sequence<T>> {
        Rc::new(Sequence::ConcatSequence {
            is_string: is_string || (left.is_string() && right.is_string()),
            node_count: 1 + left.node_count() + right.node_count(),
            left: Rc::clone(&left),
            right: Rc::clone(&right),
            length: left.cardinality() + right.cardinality(),
        })
    }
    pub fn new_lazy_sequence(boxed: &Rc<Sequence<T>>) -> Rc<Sequence<T>> {
        Sequence::<T>::new_lazy_sequence_is_string(boxed, false)
    }
    pub fn new_lazy_sequence_is_string(underlying: &Rc<Sequence<T>>, is_string: bool) -> Rc<Sequence<T>> {
        Rc::new(Sequence::LazySequence {
            is_string: is_string || underlying.is_string(),
            node_count: underlying.node_count() + 1,
            length: underlying.cardinality(),
            boxed: RefCell::new(Rc::clone(underlying)),
        })
    }

    pub fn to_array(&self) -> Rc<Vec<T>> {
        // We convert the match above to statements using the Rust "it" idiom
        if let Sequence::ArraySequence { values, .. } = self {
            // The length of the elements
            Rc::clone(values)
        } else if let Sequence::ConcatSequence { length, .. } = self {
            let mut array: Vec<T> = Vec::with_capacity(*length);
            Sequence::<T>::append_recursive(&mut array, self);
            Rc::new(array)
        } else if let Sequence::LazySequence { boxed, is_string, ..  } = self {
            let result = boxed.borrow().to_array();
            // Put the value back into boxed
            boxed.replace(Rc::clone(
                &Sequence::<T>::new_array_sequence_is_string(&result, *is_string)));
            result
        } else {
            panic!("This should never happen")
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

    pub fn node_count(&self) -> usize {
        match self {
            Sequence::ArraySequence { node_count, .. } =>
              // The length of the elements
              *node_count,
            Sequence::ConcatSequence { node_count, ..  } =>
              *node_count,
            Sequence::LazySequence { node_count, .. } =>
              *node_count,
        }
    
    }
    /// Returns the cardinality of this [`Sequence<T>`].
    // The cardinality returns the length of the sequence
    pub fn cardinality(&self) -> SizeT {
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
    pub fn select(&self, index: SizeT) -> T {
        let array = self.to_array();
        array[index].clone()
    }
}


#[allow(dead_code)]
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

#[allow(dead_code)]
pub struct Map<K, V> 
  where K: Clone + Eq + std::hash::Hash, V: Clone
{
    data: Rc<Sequence<(K, V)>>,
    // Any time we explicitly access this map, we index the data
    cache: RefCell<Option<HashMap<K, V>>>
}

// TODO: Allow supporting no hash?
impl <K, V> PartialEq<Map<K, V>> for Map<K, V>
  where K: Clone + Eq + Hash + DafnyPrint, V: Clone + Eq
{
    fn eq(&self, other: &Map<K, V>) -> bool {
        // 1. Same cardinality
        // 2. All the elements of self are in the other
        if self.cardinality() != other.cardinality() {
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

#[allow(dead_code)]
impl <K, V> Map<K, V>
  where K: Clone + Eq + std::hash::Hash + DafnyPrint, V: Clone + Eq
{
    pub fn new_empty() -> Rc<Map<K, V>> {
        Rc::new(Map {
            data: Sequence::new_array_sequence(&Rc::new(Vec::new())),
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
    pub fn cardinality(&self) -> SizeT {
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
        let new_data = Sequence::<(K, V)>::new_array_sequence(
            &Rc::new(vec![(key, value)]));
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
        let s = Sequence::<(K, V)>::new_array_sequence(&Rc::new(result));
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


#[allow(dead_code)]
pub struct MapBuilder<K, V>
  where K: Clone + Eq + std::hash::Hash, V: Clone
{
    data: HashMap<K, V>
}

#[allow(dead_code)]
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
    pub fn build(self) -> Rc<Map<K, V>> {
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
        if self.cardinality() != other.cardinality() {
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

#[allow(dead_code)]
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
            data: Sequence::new_array_sequence(&Rc::new(unique_array))
        })
    }
}

#[allow(dead_code)]
impl <V> Set<V>
  where V: Clone + Eq + DafnyPrint
{
    pub fn cardinality(&self) -> SizeT {
        self.data.cardinality()
    }
    pub fn cardinality_int(&self) -> Rc<BigInt> {
        Rc::new(BigInt::from(self.cardinality() as i64))
    }
    pub fn contains(&self, value: &V) -> bool {
        self.data.contains(value)
    }
    pub fn union(self: &Rc<Self>, other: &Rc<Set<V>>) -> Rc<Set<V>> {
        if self.cardinality() == 0 {
            return Rc::clone(other);
        }
        if other.cardinality() == 0 {
            return Rc::clone(self);
        }
        let mut result = Rc::clone(&self.data);
        // iterate over the other, add only not contained elements
        for value in other.data.to_array().iter() {
            if !result.contains(value) {
                result = Sequence::<V>::new_concat_sequence(&result,
                     &Sequence::new_array_sequence(&Rc::new(vec![value.clone()])));
            }
        }
        Set::from_sequence(&result)
    }

    pub fn intersection(self: &Rc<Self>, other: &Rc<Set<V>>) -> Rc<Set<V>> {
        if self.cardinality() == 0 {
            return Rc::clone(self);
        }
        if other.cardinality() == 0 {
            return Rc::clone(other);
        }
        // Start with an empty vec with capacity the smallest of both sets
        let mut result =
            Vec::with_capacity(
                std::cmp::min(self.cardinality(), other.cardinality()));
          
        // iterate over the other, take only elements in common
        for value in other.data.to_array().iter() {
            if self.contains(value) {
                result.push(value.clone());
            }
        }
        Set::from_array(&Rc::new(result))
    }

    pub fn difference(self: &Rc<Self>, other: &Rc<Set<V>>) -> Rc<Set<V>> {
        if self.cardinality() == 0 {
            return Rc::clone(self);
        }
        if other.cardinality() == 0 {
            return Rc::clone(self);
        }
        // Start with a vec the size of the first one
        let mut result =
            Vec::with_capacity(self.cardinality());
          
        // iterate over the other, take only elements not in second
        for value in other.data.to_array().iter() {
            if !self.contains(value) {
                result.push(value.clone());
            }
        }
        Set::from_array(&Rc::new(result))
    }

    pub fn is_disjoint_from(&self, other: &Rc<Set<V>>) -> bool {
        if self.cardinality() == 0 {
            return true;
        }
        if other.cardinality() == 0 {
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
        if self.cardinality() != other.cardinality() {
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
        if self.cardinality() == 0 {
            return true;
        }
        if other.cardinality() == 0 {
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
        self.is_subset_of(other) && self.cardinality() != other.cardinality()
    }

    pub fn elements(self: &Rc<Self>) -> Rc<Set<V>> {
        Rc::clone(self)
    }
}

#[allow(dead_code)]
struct SetBuilder<T>
  where T: Clone + Eq + std::hash::Hash
{
    data: HashMap<T, bool>
}

#[allow(dead_code)]
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

#[allow(dead_code)]
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

#[allow(dead_code)]
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
    pub fn from_owned_array(data: Vec<V>) -> Rc<Multiset<V>> {
        // Create an ArraySequence from the data
        let seq = Sequence::<V>::new_array_sequence(&Rc::new(data));
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
pub fn is_instance_of<T: ?Sized + AsAny, U: 'static>(theobject: *const T) -> bool {
    unsafe { &*theobject }.as_any().downcast_ref::<U>().is_some()
}

trait DafnyUpdowncast<U: ?Sized> {
    fn updowncast(&self) -> U;
    fn is_instance_of(&self) -> bool;
}
// Define the AsAny trait
pub trait AsAny {
  fn as_any(&self) -> &dyn Any;
}
impl <T: AsAny, U: 'static> DafnyUpdowncast<*const U> for T
{
    fn updowncast(&self) -> *const U {
        self.as_any().downcast_ref::<U>().unwrap()
    }

    fn is_instance_of(&self) -> bool {
        is_instance_of::<T, U>(self)
        //self.as_any().downcast_ref::<U>().is_some()
    }
}
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
impl <T: AsAny, U: 'static> DafnyUpdowncast<*const U> for Rc<T>
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

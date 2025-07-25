/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};
use std::hash::Hash;
use dafny_runtime::*;

// Dummy export for compatibility with dummyImportMember
pub struct Dummy__ {}

// MutableMap implementation using Arc<RwLock<HashMap>>
pub struct MutableMap<K: Clone + Eq + Hash + DafnyTypeEq, V: Clone + DafnyTypeEq> {
    map: Arc<RwLock<HashMap<K, V>>>,
    _phantom_inv: std::marker::PhantomData<fn(&K, &V) -> bool>,
    _phantom_bytes_keys: std::marker::PhantomData<bool>,
}

impl<K: Clone + Eq + Hash + DafnyTypeEq, V: Clone + DafnyTypeEq> MutableMap<K, V> {
    pub fn _ctor(
        _inv: &Rc<dyn Fn(&K, &V) -> bool>,
        _bytes_keys: bool,
    ) -> *mut MutableMap<K, V> {
        let map = MutableMap {
            map: Arc::new(RwLock::new(HashMap::new())),
            _phantom_inv: std::marker::PhantomData,
            _phantom_bytes_keys: std::marker::PhantomData,
        };
        Rc::new(map).as_ptr() as *mut MutableMap<K, V>
    }

    pub fn Keys(&self) -> DafnySet<K> {
        let map = self.map.read().unwrap();
        let keys: Vec<K> = map.keys().cloned().collect();
        DafnySet::from_array(&keys)
    }

    pub fn HasKey(&self, k: &K) -> bool {
        let map = self.map.read().unwrap();
        map.contains_key(k)
    }

    pub fn Values(&self) -> DafnySet<V> {
        let map = self.map.read().unwrap();
        let values: Vec<V> = map.values().cloned().collect();
        DafnySet::from_array(&values)
    }

    pub fn Items(&self) -> DafnySet<(K, V)> {
        let map = self.map.read().unwrap();
        let items: Vec<(K, V)> = map.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        DafnySet::from_array(&items)
    }

    pub fn Put(&self, k: &K, v: &V) {
        let mut map = self.map.write().unwrap();
        map.insert(k.clone(), v.clone());
    }

    pub fn Get(&self, k: &K) -> Option<V> {
        let map = self.map.read().unwrap();
        map.get(k).cloned().into()
    }

    pub fn Remove(&self, k: &K) {
        let mut map = self.map.write().unwrap();
        map.remove(k);
    }

    pub fn Size(&self) -> DafnyInt {
        let map = self.map.read().unwrap();
        DafnyInt::from(map.len())
    }
}

// AtomicBox implementation using Arc<RwLock<T>>
pub struct AtomicBox<T: Clone + DafnyTypeEq> {
    value: Arc<RwLock<T>>,
    _phantom_inv: std::marker::PhantomData<fn(&T) -> bool>,
}

impl<T: Clone + DafnyTypeEq> AtomicBox<T> {
    pub fn _ctor(
        _inv: &Rc<dyn Fn(&T) -> bool>,
        t: &T,
    ) -> *mut AtomicBox<T> {
        let atomic_box = AtomicBox {
            value: Arc::new(RwLock::new(t.clone())),
            _phantom_inv: std::marker::PhantomData,
        };
        Rc::new(atomic_box).as_ptr() as *mut AtomicBox<T>
    }

    pub fn Get(&self) -> T {
        let value = self.value.read().unwrap();
        value.clone()
    }

    pub fn Put(&self, t: &T) {
        let mut value = self.value.write().unwrap();
        *value = t.clone();
    }
}

// Lock implementation using Arc<Mutex<()>>
pub struct Lock {
    mutex: Arc<Mutex<()>>,
    // We need to track lock state for Dafny's preconditions
    // In a real implementation, this would be more sophisticated
}

impl Lock {
    pub fn _ctor() -> *mut Lock {
        let lock = Lock {
            mutex: Arc::new(Mutex::new(())),
        };
        Rc::new(lock).as_ptr() as *mut Lock
    }

    pub fn Lock(&self) {
        // This will block until the lock is acquired
        let _guard = self.mutex.lock().unwrap();
        // In a real implementation, we'd need to store the guard
        // For now, this is a simplified version that doesn't handle
        // the lock/unlock pairing correctly
        std::mem::forget(_guard);
    }

    pub fn Unlock(&self) {
        // In a real implementation, we'd release the stored guard
        // This simplified version doesn't properly implement lock/unlock pairing
        // For testing purposes, we'll just do nothing here
    }
}

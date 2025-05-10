package Std.Concurrent;

import dafny.*;
import Std.Wrappers.*;

import java.math.BigInteger;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.Map;

public class MutableMap<K, V> {

    private ConcurrentHashMap<K, V> map;
    private dafny.TypeDescriptor<V> td_V; 

    public MutableMap(dafny.TypeDescriptor<K> td_K, dafny.TypeDescriptor<V> td_V) {
        this.td_V = td_V;
        map = new ConcurrentHashMap<K, V>();
    }
    public void __ctor(boolean bytesKeys) { }

    public dafny.DafnySet<K> Keys() {
        return new dafny.DafnySet<K>(Collections.list(map.keys()));
    }

    public boolean HasKey(K k) {
        return map.containsKey(k);
    }

    public dafny.DafnySet<V> Values() {
        return new dafny.DafnySet<V>(map.values());
    }

    public dafny.DafnySet<dafny.Tuple2<K, V>> Items() {
        Set<Map.Entry<K, V>> set = map.entrySet();
        Set<dafny.Tuple2<K, V>> tupleSet = new HashSet<dafny.Tuple2<K, V>>();
        set.forEach(e -> tupleSet.add(dafny.Tuple2.create(e.getKey(), e.getValue())));
        return new dafny.DafnySet<dafny.Tuple2<K, V>>(tupleSet);
    }

    public void Put(K k, V v) {
        map.put(k, v);
    }

    public Std.Wrappers.Option<V> Get(K k) {
        V v = map.get(k);
        if (v == null) {
            return Std.Wrappers.Option.create_None(td_V);
        } else {
            return Std.Wrappers.Option.create_Some(td_V, v);
        }
    }

    public void Remove(K k) {
        map.remove(k);
    }

    public BigInteger Size() {
        return BigInteger.valueOf(map.size());
    }
}

package DafnyStdLibsExterns.Concurrent;

import dafny.*;
import DafnyStdLibs.Wrappers.*;

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

    public dafny.DafnySet<K> Keys() {
        return new dafny.DafnySet(Collections.list(map.keys()));
    }

    public boolean HasKey(K k) {
        return map.containsKey(k);
    }

    public dafny.DafnySet<V> Values() {
        return new dafny.DafnySet(map.values());
    }

    public dafny.DafnySet<dafny.Tuple2<K, V>> Items() {
        Set<Map.Entry<K, V>> set = map.entrySet();
        Set<dafny.Tuple2<K, V>> tupleSet = new HashSet<dafny.Tuple2<K, V>>();
        set.forEach(e -> tupleSet.add(dafny.Tuple2.create(e.getKey(), e.getValue())));
        return new dafny.DafnySet(tupleSet);
    }

    public void Put(K k, V v) {
        map.put(k, v);
    }

    public DafnyStdLibs.Wrappers.Option<V> Get(K k) {
        var v = map.get(k);
        if (v == null) {
            return DafnyStdLibs.Wrappers.Option.create_None(td_V);
        } else {
            return DafnyStdLibs.Wrappers.Option.create_Some(td_V, v);
        }
    }

    public void Remove(K k) {
        map.remove(k);
    }

    public BigInteger Size() {
        return BigInteger.valueOf(map.size());
    }
}
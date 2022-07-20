// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

package dafny;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

public class DafnyMap<K, V> {
    private Map<K, V> innerMap;

    public DafnyMap() {
        innerMap = new HashMap<>();
    }

    private DafnyMap(HashMap<K, V> innerMap) {
        this.innerMap = innerMap;
    }

    public DafnyMap(Map<K, V> m) {
        assert m != null : "Precondition Violation";
        innerMap = new HashMap<>();
        m.forEach((k, v) -> innerMap.put(k, v));
    }

    public static <K, V> DafnyMap<K, V> empty() { return new DafnyMap<K, V>(); }

    @SuppressWarnings("unchecked")
    public static <K, V> DafnyMap<K, V> fromElements(Tuple2<K, V> ... pairs) {
        DafnyMap<K, V> result = new DafnyMap<K, V>();
        for (Tuple2<K, V> pair : pairs) {
            result.innerMap.put(pair.dtor__0(), pair.dtor__1());
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    public static <K, V> TypeDescriptor<DafnyMap<? extends K, ? extends V>> _typeDescriptor(
            TypeDescriptor<K> keyType, TypeDescriptor<V> valueType) {
        // Fudge the type parameters; it's not great, but it's safe because
        // (for now) type descriptors are only used for default values
        return TypeDescriptor.referenceWithDefault(
                (Class<DafnyMap<? extends K, ? extends V>>) (Class<?>) DafnyMap.class,
                DafnyMap.empty());
    }

    public boolean contains(Object t) {
        return innerMap.containsKey(t);
    }

    public static <K, V> DafnyMap<K, V> update(DafnyMap<? extends K, ? extends V> th, K k, V v) {
        HashMap<K, V> copy = new HashMap<>(th.innerMap);
        copy.put(k, v);
        DafnyMap<K, V> r = new DafnyMap<>();
        r.innerMap = copy;
        return r;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (obj == null) return false;
        if (getClass() != obj.getClass()) return false;
        DafnyMap o = (DafnyMap) obj;
        return innerMap.equals(o.innerMap);
    }

    @Override
    public int hashCode() {
        return innerMap.hashCode();
    }

    @Override
    public String toString() {
        String s = "map[";
        String sep = "";
        for (Map.Entry<K, V> entry : innerMap.entrySet()) {
            s += sep + Helpers.toString(entry.getKey()) + " := " + Helpers.toString(entry.getValue());
            sep = ", ";
        }
        return s + "]";
    }

    public void forEach(BiConsumer<? super K, ? super V> action) {
        innerMap.forEach(action);
    }

    @SuppressWarnings("unchecked")
    public static <K, V> DafnyMap<? extends K, ? extends V> merge(DafnyMap<? extends K, ? extends V> th, DafnyMap<? extends K, ? extends V> other) {
        assert th != null : "Precondition Violation";
        assert other != null : "Precondition Violation";

        if (th.isEmpty()) {
            return (DafnyMap<K, V>)other;
        } else if (other.isEmpty()) {
            return (DafnyMap<K, V>)th;
        }

        Map<K, V> m = new HashMap<K, V>(other.innerMap);
        th.forEach((k, v) -> {
                if (!m.containsKey(k)) {
                    m.put(k, v);
                }
            });
        return new DafnyMap<K, V>(m);
    }

    @SuppressWarnings("unchecked")
    public static <K, V> DafnyMap<? extends K, ? extends V> subtract(DafnyMap<? extends K, ? extends V> th, DafnySet<? extends K> keys) {
        assert th != null : "Precondition Violation";
        assert keys != null : "Precondition Violation";

        if (th.isEmpty() || keys.isEmpty()) {
            return (DafnyMap<K, V>)th;
        }

        Map<K, V> m = new HashMap(th.innerMap);
        for (K k : keys.Elements()) {
            m.remove(k);
        }
        return new DafnyMap<K, V>(m);
    }

    public int size() {
        return innerMap.size();
    }

    public int cardinalityInt() {
        return size();
    }

    public boolean isEmpty() {
        return innerMap.isEmpty();
    }

    public V get(Object key) {
        return innerMap.get(key);
    }

    public DafnySet<K> keySet() {
        return new DafnySet<>(innerMap.keySet());
    }

    public DafnySet<V> valueSet() {
        return new DafnySet<>(innerMap.values());
    }

    // Until tuples (and other datatypes) are compiled with type-argument variance, the following
    // method takes type parameters <KK, VV>. The expectation is that <K, V> is <? extends KK, ? extends VV>.
    @SuppressWarnings("unchecked")
    public <KK, VV> DafnySet<? extends Tuple2<KK, VV>> entrySet() {
        ArrayList<Tuple2<K, V>> list = new ArrayList<Tuple2<K, V>>();
        for (Map.Entry<K, V> entry : innerMap.entrySet()) {
            list.add(new Tuple2<K, V>(entry.getKey(), entry.getValue()));
        }
        return (DafnySet<? extends Tuple2<KK, VV>>)(Object)new DafnySet<Tuple2<K, V>>(list);
    }
}

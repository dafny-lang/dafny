package dafny;

import java.util.*;
import java.util.function.BiConsumer;
import java.util.function.BiFunction;
import java.util.function.Function;

public class DafnyMap<K, V> implements Map<K, V> {
    private Map<K, V> innerMap;

    public DafnyMap() {
        innerMap = new HashMap<>();
    }

    public DafnyMap(Map<K, V> m) {
        assert m != null : "Precondition Violation";
        innerMap = new HashMap<>();
        m.forEach((k, v) -> put(k, v));
    }

    public static <K, V> DafnyMap<K, V> empty() { return new DafnyMap<K, V>(); }

    public static <K, V> DafnyMap<K, V> fromElements(Tuple2<K, V> ... pairs) {
        DafnyMap<K, V> result = new DafnyMap<K, V>();
        for (Tuple2<K, V> pair : pairs) {
            result.put(pair.dtor__0(), pair.dtor__1());
        }
        return result;
    }

    @SuppressWarnings("unchecked")
    public static <K, V> Type<DafnyMap<? extends K, ? extends V>> _type(
            Type<K> keyType, Type<V> valueType) {
        // Fudge the type parameters; it's not great, but it's safe because
        // (for now) type descriptors are only used for default values
        return Type.referenceWithDefault(
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
    protected Object clone() throws CloneNotSupportedException {
        return super.clone();
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
        for (Entry<K, V> entry : innerMap.entrySet()) {
            s += sep + Helpers.toString(entry.getKey()) + " := " + Helpers.toString(entry.getValue());
            sep = ", ";
        }
        return s + "]";
    }

    @Override
    public void forEach(BiConsumer<? super K, ? super V> action) {
        innerMap.forEach(action);
    }

    @Override
    public void replaceAll(BiFunction<? super K, ? super V, ? extends V> function) {
        innerMap.replaceAll(function);
    }

    @Override
    public V getOrDefault(Object key, V defaultValue) {
        return innerMap.getOrDefault(key, defaultValue);
    }

    @Override
    public V putIfAbsent(K key, V value) {
        return innerMap.putIfAbsent(key, value);
    }

    @Override
    public boolean remove(Object key, Object value) {
        return innerMap.remove(key, value);
    }

    @Override
    public boolean replace(K key, V oldValue, V newValue) {
        return innerMap.replace(key, oldValue, newValue);
    }

    @Override
    public V replace(K key, V value) {
        return innerMap.replace(key, value);
    }

    @Override
    public V computeIfAbsent(K key, Function<? super K, ? extends V> mappingFunction) {
        return innerMap.computeIfAbsent(key, mappingFunction);
    }

    @Override
    public V computeIfPresent(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        return innerMap.computeIfPresent(key, remappingFunction);
    }

    @Override
    public V compute(K key, BiFunction<? super K, ? super V, ? extends V> remappingFunction) {
        return innerMap.compute(key, remappingFunction);
    }

    @Override
    public V merge(K key, V value, BiFunction<? super V, ? super V, ? extends V> remappingFunction) {
        return innerMap.merge(key, value, remappingFunction);
    }

    @Override
    public int size() {
        return innerMap.size();
    }

    public int cardinalityInt() {
        return size();
    }

    @Override
    public boolean isEmpty() {
        return innerMap.isEmpty();
    }

    @Override
    public boolean containsKey(Object key) {
        return innerMap.containsKey(key);
    }

    @Override
    public boolean containsValue(Object value) {
        return innerMap.containsValue(value);
    }

    @Override
    public V get(Object key) {
        return innerMap.get(key);
    }

    @Override
    public V put(K key, V value) {
        return innerMap.put(key, value);
    }

    @Override
    public V remove(Object key) {
        return innerMap.remove(key);
    }

    @Override
    public void putAll(Map<? extends K, ? extends V> m) {
        innerMap.putAll(m);
    }

    @Override
    public void clear() {
        innerMap.clear();
    }

    @Override
    public Set<K> keySet() {
        return innerMap.keySet();
    }

    @Override
    public Collection<V> values() {
        return new HashSet<>(innerMap.values());
    }

    @Override
    public Set<Entry<K, V>> entrySet() {
        return innerMap.entrySet();
    }

    public DafnySet<K> dafnyKeySet() {
        return new DafnySet<>(innerMap.keySet());
    }

    public DafnySet<V> dafnyValues() {
        return new DafnySet<>(innerMap.values());
    }

    // Until tuples (and other datatypes) are compiled with type-argument variance, the following
    // method takes type parameters <KK, VV>. The expectation is that <K, V> is <? extends KK, ? extends VV>.
    public <KK, VV> DafnySet<? extends Tuple2<KK, VV>> dafnyEntrySet() {
        ArrayList<Tuple2<K, V>> list = new ArrayList<Tuple2<K, V>>();
        for (Entry<K, V> entry : innerMap.entrySet()) {
            list.add(new Tuple2<K, V>(entry.getKey(), entry.getValue()));
        }
        return (DafnySet<? extends Tuple2<KK, VV>>)(Object)new DafnySet<Tuple2<K, V>>(list);
    }
}

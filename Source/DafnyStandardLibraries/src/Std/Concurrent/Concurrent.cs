namespace Std.Concurrent {
    using System.Collections.Concurrent;
    using Std.Wrappers;

    public class MutableMap<K, V> {

        private ConcurrentDictionary<K, V> map;

        public MutableMap(bool bytesKeys) {
            map = new ConcurrentDictionary<K, V>();
        }

        public void __ctor() { }

        public Dafny.ISet<K> Keys() {
            return Dafny.Set<K>.FromCollection(map.Keys);
        }

        public bool HasKey(K k) {
            return map.ContainsKey(k);
        }

        public Dafny.ISet<V> Values() {
            return Dafny.Set<V>.FromCollection(map.Values);
        }
        public Dafny.ISet<_System._ITuple2<K, V>> Items() {
            System.Collections.Generic.IEnumerable<_System._ITuple2<K, V>> ToEnumerable(System.Collections.Generic.IEnumerator<System.Collections.Generic.KeyValuePair<K, V>> enumerator) {
                while (enumerator.MoveNext())
                    yield return  _System.Tuple2<K, V>.create(enumerator.Current.Key, enumerator.Current.Value);
            }

            return Dafny.Set<_System._ITuple2<K, V>>.FromCollection(ToEnumerable(map.GetEnumerator()));
        }

        public void Put(K k, V v) {
            map.AddOrUpdate(k, v, ((key, oldValue) => v));
        }

        public _IOption<V> Get(K k) {
            var v = map[k];
            if (v is null) {
                return Option<V>.create_None();
            } else {
                return Option<V>.create_Some(v);
            }
        }

        public void Remove(K k) {
            map.TryRemove(k, out _);
        }

        public System.Numerics.BigInteger Size() {
            return new System.Numerics.BigInteger(map.Count);
        }
    }

    public class AtomicBox<T> {

        private T val;
        private Lock l;

        public AtomicBox() {
            l = new Lock();
        }

        public void __ctor(T t) {
          val = t;
        }

        public void Put(T t) {
            l.__Lock();
            val = t;
            l.Unlock();
        }

        public T Get() {
            l.__Lock();
            var r = val;
            l.Unlock();
            return r;
        }
    }

    public class Lock {

        private static System.Threading.Mutex mut = new System.Threading.Mutex();

        public void __ctor() {
        }

        public void __Lock() {
            mut.WaitOne();
        }

        public void Unlock() {
            mut.ReleaseMutex();
        }
    }
}
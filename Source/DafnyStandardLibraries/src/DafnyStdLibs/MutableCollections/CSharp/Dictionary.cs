using System.Collections.Generic;
using System.Numerics;

namespace System.Collections.Generic {
  partial class __default {
    public static BigInteger DictionaryLength<K,V>(IDictionary<K,V> dic) {
      return dic.Count;
    }

    public static void DictionarySet<K,V>(IDictionary<K,V> dic, K k, V v) {
      dic[k] = v;
    }

    public static V DictionaryGet<K,V>(IDictionary<K,V> dic, K k) {
      return dic[k];
    }
  }
}
using System;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;

namespace Microsoft.Dafny;

public static class Dictionaries {
  public static ImmutableDictionary<TKey, TValue> Merge<TKey, TValue>(this ImmutableDictionary<TKey, TValue> original,
    IEnumerable<KeyValuePair<TKey, TValue>> addition, Func<TValue, TValue, TValue> mergeValues) {
    var result = original;
    foreach (var (key, value) in addition) {
      var newValue = original.TryGetValue(key, out var originalValue)
        ? mergeValues(originalValue, value) : value;
      result = result.SetItem(key, newValue);
    }
    return result;
  }
}
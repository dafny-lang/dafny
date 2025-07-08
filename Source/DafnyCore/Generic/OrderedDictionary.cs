using System;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public class OrderedDictionary<TKey, TValue> {
  private readonly Dictionary<TKey, TValue> keyToValue = new();
  private readonly List<TKey> keyOrder = [];
  private readonly Func<TValue, TKey> getKey;

  public OrderedDictionary(Func<TValue, TKey> getKey) {
    this.getKey = getKey;
  }
  public IEnumerable<TValue> Values => keyOrder.Select(key => keyToValue[key]);

  public void AddRange(IEnumerable<TValue> values) {
    foreach (var value in values) {
      Add(value);
    }
  }

  public TValue GetOrAdd(TValue value) {
    var key = getKey(value);
    return GetOrCreate(key, () => value);
  }

  public TValue GetOrCreate(TKey key, Func<TValue> createValue) {
    if (keyToValue.TryGetValue(key, out var result)) {
      return result;
    }

    result = createValue();
    keyToValue[key] = result;
    keyOrder.Add(key);
    return result;
  }

  public void Add(TValue value) {
    var key = getKey(value);
    keyOrder.Add(key);
    keyToValue[key] = value;
  }

  public TValue GetValueOrDefault(TKey key) {
    return keyToValue.GetValueOrDefault(key);
  }

  public int Count => keyOrder.Count;
}
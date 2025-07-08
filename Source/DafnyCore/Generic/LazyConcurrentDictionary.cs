#nullable enable
using System;
using System.Collections;
using System.Collections.Concurrent;
using System.Collections.Generic;

namespace Microsoft.Dafny;

/// <summary>
/// System.Collections.Concurrent.ConcurrentDictionary does not allow you to lazily add a value if it is missing,
/// in a way that guarantees only running the lazy computation once.
/// </summary>
public class LazyConcurrentDictionary<TKey, TValue> : IEnumerable<KeyValuePair<TKey, TValue>>
  where TKey : notnull {
  private readonly ConcurrentDictionary<TKey, Lazy<TValue>> underlyingDictionary = new();

  public TValue GetOrAdd(TKey key, Func<TValue> computeValue) {
    var lazyResult = underlyingDictionary.GetOrAdd(key, new Lazy<TValue>(computeValue));
    return lazyResult.Value;
  }

  public IEnumerator<KeyValuePair<TKey, TValue>> GetEnumerator() {
    return new Enumerator(underlyingDictionary.GetEnumerator());
  }

  class Enumerator : IEnumerator<KeyValuePair<TKey, TValue>> {
    private readonly IEnumerator<KeyValuePair<TKey, Lazy<TValue>>> underlying;

    public Enumerator(IEnumerator<KeyValuePair<TKey, Lazy<TValue>>> underlying) {
      this.underlying = underlying;
    }

    public bool MoveNext() {
      return underlying.MoveNext();
    }

    public void Reset() {
      underlying.Reset();
    }

    public KeyValuePair<TKey, TValue> Current => new(underlying.Current.Key, underlying.Current.Value.Value);

    object IEnumerator.Current => Current;

    public void Dispose() {
      underlying.Dispose();
    }
  }

  IEnumerator IEnumerable.GetEnumerator() {
    return GetEnumerator();
  }

  public bool TryGetValue(TKey key, out TValue? value) {
    if (underlyingDictionary.TryGetValue(key, out var lazyValue)) {
      value = lazyValue.Value;
      return true;
    }

    value = default;
    return false;
  }

  public TValue this[TKey key] => underlyingDictionary[key].Value;

  public bool Remove(TKey key) {
    return underlyingDictionary.TryRemove(key, out _);
  }
}
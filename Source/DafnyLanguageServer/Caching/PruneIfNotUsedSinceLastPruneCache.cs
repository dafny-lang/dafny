using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny; 

public class PruneIfNotUsedSinceLastPruneCache<TKey, TValue>
  where TValue : class
  where TKey : notnull {
  class Item {
    public Item(TValue value) {
      Value = value;
      Accessed = true;
    }

    public bool Accessed { get; set; }
    public TValue Value { get; }
  }

  private readonly ConcurrentDictionary<TKey, Item> items;

  public IEnumerable<TValue> Values => items.Select(i => i.Value.Value);

  public PruneIfNotUsedSinceLastPruneCache(IEqualityComparer<TKey> comparer) {
    items = new(comparer);
  }

  public void Prune() {
    var keys = items.Keys.ToList();
    foreach (var key in keys) {
      var item = items[key];
      if (!item.Accessed) {
        items.TryRemove(key, out _);
      }

      item.Accessed = false;
    }
  }

  public void Set(TKey key, TValue value) {
    items.TryAdd(key, new Item(value));
  }

  public bool TryGet(TKey key, out TValue? value) {
    var result = items.TryGetValue(key, out var item);
    if (result) {
      value = item!.Value;
      item.Accessed = true;
    } else {
      value = null;
    }

    return result;
  }
}
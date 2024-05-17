using System;
using System.Collections.Concurrent;
using System.Collections.Generic;
using System.Collections.Immutable;
using System.Linq;
using System.Threading;
using System.Threading.Tasks;
using Microsoft.Dafny.LanguageServer.Workspace;

namespace Microsoft.Dafny;

public record PruneResult<T>(T Result, int Pruned, int Hits, int Total);

public class PruneIfNotUsedSinceLastPruneCache<TKey, TValue>
  where TValue : class
  where TKey : notnull {
  private SemaphoreSlim semaphoreSlim = new(1);


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
  public int Count => items.Count;

  public PruneIfNotUsedSinceLastPruneCache(IEqualityComparer<TKey> comparer) {
    items = new(comparer);
  }

  public async Task<PruneResult<T>> UseAndPrune<T>(Func<Task<T>> use, CancellationToken cancellationToken) {
    await semaphoreSlim.WaitAsync(cancellationToken);
    try {
      var before = Count;
      var result = await use();
      var pruned = Prune();
      var hits = before - pruned;

      return new PruneResult<T>(result, pruned, hits, Count);
    }
    finally {
      semaphoreSlim.Release();
    }
  }

  private int Prune() {
    var keys = items.Keys.ToList();
    var removedCount = 0;
    foreach (var key in keys) {
      var item = items[key];
      if (!item.Accessed) {
        items.TryRemove(key, out _);
        removedCount++;
      }

      item.Accessed = false;
    }

    return removedCount;
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
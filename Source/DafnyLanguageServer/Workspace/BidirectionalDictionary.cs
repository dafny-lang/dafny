using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Workspace;

class BidirectionalDictionary<TKey, TValue> where TKey : notnull where TValue : notnull {
  private readonly Dictionary<TKey, TValue> forwards = new();
  private readonly Dictionary<TValue, ISet<TKey>> backwards = new();

  public IEnumerable<TKey> Backwards(TValue value) {
    return BackwardsInner(value);
  }

  private ISet<TKey> BackwardsInner(TValue value)
  {
    return backwards.GetOrCreate(value, () => new HashSet<TKey>());
  }

  public TValue Forwards(TKey key) {
    return forwards[key];
  }

  public void Add(TKey key, TValue value) {
    forwards[key] = value;
    var set = BackwardsInner(value);
    set.Add(key);
  }

  public bool Remove(TKey key, out bool lastValueEntry, out TValue value) {
    if (forwards.Remove(key, out value!)) {
      var set = backwards[value];
      set.Remove(key);
      lastValueEntry = !set.Any();
      return true;
    }

    lastValueEntry = false;
    return false;
  }

  public bool TryGetValue(TKey key, out TValue value) {
    return forwards.TryGetValue(key, out value!);
  }
}
using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  /// <summary>
  /// A scope consists of a set of identifiers.
  /// Two scopes overlap if the intersections of their identifiers is not empty
  /// </summary>
  public class VisibilityScope {
    private static uint maxScopeId;

    private readonly SortedSet<uint> scopeTokens = [];

    // Only for debugging
    private readonly SortedSet<string> scopeIds = [];

    private static bool Overlaps(SortedSet<uint> set1, SortedSet<uint> set2) {
      // This conditional implements a performance optimization,
      // since there is an iteration over the second argument to Overlaps
      if (set1.Count < set2.Count) {
        return set2.Overlaps(set1);
      } else {
        return set1.Overlaps(set2);
      }
    }

    private Dictionary<VisibilityScope, Tuple<int, bool>> cached = new();

    // By convention, the "null" scope sees all
    public bool VisibleInScope(VisibilityScope other) {
      if (other != null) {
        if (cached.TryGetValue(other, out var result)) {
          if (result.Item1 == other.scopeTokens.Count) {
            // If the second scope did not change, then we can use the cached result.
            // If this scoped changed, the cache would have been cleared.
            return result.Item2;
          } else {
            // If the scoped used to overlap, they still do, since scopes only grow.
            if (result.Item2) {
              return true;
            }
          }
        }
        var overlaps = Overlaps(other.scopeTokens, scopeTokens);
        cached[other] = new Tuple<int, bool>(other.scopeTokens.Count, overlaps);
        return overlaps;

      }
      return true;
    }

    [Pure]
    public bool IsEmpty() {
      return scopeTokens.Count == 0;
    }

    //However augmenting with a null scope does nothing
    public void Augment(VisibilityScope other) {
      if (other != null) {
        scopeTokens.UnionWith(other.scopeTokens);
        scopeIds.UnionWith(other.scopeIds);
        cached.Clear();
      }
    }

    public VisibilityScope(string name) {
      scopeTokens.Add(maxScopeId);
      scopeIds.Add(name);
      if (maxScopeId == uint.MaxValue) {
        Contract.Assert(false);
      }
      maxScopeId++;
    }

    public VisibilityScope() {
    }
  }
}
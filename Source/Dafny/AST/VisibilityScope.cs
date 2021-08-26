using System;
using System.Collections.Generic;
using System.Diagnostics.Contracts;

namespace Microsoft.Dafny {
  public class VisibilityScope {
    private static uint maxScopeID = 0;

    private SortedSet<uint> scopeTokens = new SortedSet<uint>();

    // Only for debugging
    private SortedSet<string> scopeIds = new SortedSet<string>();

    private bool overlaps(SortedSet<uint> set1, SortedSet<uint> set2) {
      if (set1.Count < set2.Count) {
        return set2.Overlaps(set1);
      } else {
        return set1.Overlaps(set2);
      }
    }

    private Dictionary<VisibilityScope, Tuple<int, bool>> cached = new Dictionary<VisibilityScope, Tuple<int, bool>>();

    //By convention, the "null" scope sees all
    public bool VisibleInScope(VisibilityScope other) {
      if (other != null) {
        Tuple<int, bool> result;
        if (cached.TryGetValue(other, out result)) {
          if (result.Item1 == other.scopeTokens.Count) {
            return result.Item2;
          } else {
            if (result.Item2) {
              return true;
            }
          }
        }
        var isoverlap = overlaps(other.scopeTokens, this.scopeTokens);
        cached[other] = new Tuple<int, bool>(other.scopeTokens.Count, isoverlap);
        return isoverlap;

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
      scopeTokens.Add(maxScopeID);
      scopeIds.Add(name);
      if (maxScopeID == uint.MaxValue) {
        Contract.Assert(false);
      }
      maxScopeID++;
    }

    public VisibilityScope() {
    }

  }
}
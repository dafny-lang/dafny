using System;
using System.Collections.Generic;

namespace DafnyCore.Generic;

public class PredicateEqualityComparer<T> : IEqualityComparer<T> {
  private readonly Func<T, T, bool> comparer;

  public PredicateEqualityComparer(Func<T, T, bool> comparer) {
    this.comparer = comparer;
  }

  public bool Equals(T a, T b) {
    return comparer(a, b);
  }

  public int GetHashCode(T a) {
    return a.GetHashCode();
  }
}
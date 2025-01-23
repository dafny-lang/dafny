using System;
using System.Collections.Generic;

namespace DafnyCore.Generic;

public class PredicateEqualityComparer<T>(Func<T, T, bool> comparer) : IEqualityComparer<T> {
  public bool Equals(T a, T b) {
    return comparer(a, b);
  }

  public int GetHashCode(T a) {
    return a.GetHashCode();
  }
}
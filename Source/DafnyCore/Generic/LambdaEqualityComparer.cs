using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

public class LambdaEqualityComparer<T>(Func<T, T, bool> equals, Func<T, int> hashCode) : IEqualityComparer<T> {
  public bool Equals(T x, T y) {
    return equals(x, y);
  }

  public int GetHashCode(T obj) {
    return hashCode(obj);
  }
}
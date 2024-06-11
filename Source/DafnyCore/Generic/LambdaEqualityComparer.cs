using System;
using System.Collections.Generic;

namespace Microsoft.Dafny;

public class LambdaEqualityComparer<T> : IEqualityComparer<T> {
  private readonly Func<T, T, bool> equals;
  private readonly Func<T, int> hashCode;

  public LambdaEqualityComparer(Func<T, T, bool> equals, Func<T, int> hashCode) {
    this.equals = equals;
    this.hashCode = hashCode;
  }

  public bool Equals(T x, T y) {
    return equals(x, y);
  }

  public int GetHashCode(T obj) {
    return hashCode(obj);
  }
}
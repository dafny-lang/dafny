using System;
using System.Collections.Generic;
using System.Linq;
using System.Reflection;

namespace Microsoft.Dafny;

public interface IPointer<T> {
  T Get();
  void Set(T value);
}

record Pointer<T>(Func<T> Get, Action<T> Set) : IPointer<T> {
  T IPointer<T>.Get() {
    return Get();
  }

  void IPointer<T>.Set(T value) {
    Set(value);
  }
}

public static class PointerExtensions {
  public static IEnumerable<IPointer<T>> ToPointers<T>(this IList<T> values) {
    return Enumerable.Range(0, values.Count)
      .Select(index => new Pointer<T>(() => values[index],
        value => values[index] = value));
  }
}
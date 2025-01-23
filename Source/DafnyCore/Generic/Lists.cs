using System.Collections;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

public static class Lists {
  public static IReadOnlyList<T> Concat<T>(this IReadOnlyList<T> left, IReadOnlyList<T> right) {
    return new ConcatReadOnlyLists<T>(left, right);
  }
}

public class ConcatReadOnlyLists<T>(IReadOnlyList<T> left, IReadOnlyList<T> right) : IReadOnlyList<T> {
  public IReadOnlyList<T> Left { get; } = left;
  public IReadOnlyList<T> Right { get; } = right;

  public IEnumerator<T> GetEnumerator() {
    return Enumerable.Range(0, Count).Select(index => this[index]).GetEnumerator();
  }

  IEnumerator IEnumerable.GetEnumerator() {
    return GetEnumerator();
  }

  public int Count { get; private set; } = left.Count + right.Count;

  public T this[int index] => index < Left.Count ? Left[index] : Right[index - Left.Count];
}
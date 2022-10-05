using System.Collections;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

class LinkedListEnumerator<T> : IEnumerator<T> {
  private Cons<T> cons;

  public LinkedListEnumerator(Cons<T> cons) {
    this.cons = cons;
  }

  public bool MoveNext() {
    if (cons.Tail is Cons<T> tailCons) {
      cons = tailCons;
      return true;
    }

    return false;
  }

  public void Reset() {
    throw new System.NotSupportedException();
  }

  public T Current => cons.Head;

  object IEnumerator.Current => Current;

  public void Dispose() {
  }
}
public abstract record LinkedList<T> : IEnumerable<T> {
  public abstract IEnumerator<T> GetEnumerator();
  IEnumerator IEnumerable.GetEnumerator() {
    return GetEnumerator();
  }
}

public static class LinkedLists {
  public static LinkedList<T> Concat<T>(IEnumerable<T> left, LinkedList<T> right) {
    LinkedList<T> result = right;
    foreach (var value in left.Reverse()) {
      result = new Cons<T>(value, result);
    }

    return result;
  }

  public static LinkedList<T> Create<T>(params T[] values) {
    return Concat(values, new Nil<T>());
  }
}

public record Cons<T>(T Head, LinkedList<T> Tail) : LinkedList<T> {
  public override IEnumerator<T> GetEnumerator() {
    return new LinkedListEnumerator<T>(this);
  }
}

public record Nil<T>() : LinkedList<T> {
  public override IEnumerator<T> GetEnumerator() {
    return Enumerable.Empty<T>().GetEnumerator();
  }
}
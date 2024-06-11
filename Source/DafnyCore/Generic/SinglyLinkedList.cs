using System;
using System.Collections;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny;

class LinkedListEnumerator<T> : IEnumerator<T> {
  private Cons<T> list;

  public LinkedListEnumerator(Cons<T> list) {
    this.list = new Cons<T>(default, list);
  }

  public bool MoveNext() {
    if (list.Tail is Cons<T> tailCons) {
      list = tailCons;
      return true;
    }

    return false;
  }

  public void Reset() {
    throw new System.NotSupportedException();
  }

  public T Current => list.Head;

  object IEnumerator.Current => Current;

  public void Dispose() {
  }
}

public abstract record SinglyLinkedList<T> : IEnumerable<T> {
  public abstract IEnumerator<T> GetEnumerator();
  IEnumerator IEnumerable.GetEnumerator() {
    return GetEnumerator();
  }

  public bool Any() {
    return this is not Nil<T>;
  }
}

public static class LinkedLists {
  public static SinglyLinkedList<T> Concat<T>(SinglyLinkedList<T> left, SinglyLinkedList<T> right) {
    return left switch {
      Nil<T> => right,
      Cons<T> cons => new Cons<T>(cons.Head, Concat<T>(cons.Tail, right)),
      _ => throw new ArgumentOutOfRangeException(nameof(left))
    };
  }


  public static SinglyLinkedList<T> FromList<T>(IReadOnlyList<T> values, SinglyLinkedList<T> tail = null) {
    SinglyLinkedList<T> result = tail ?? new Nil<T>();
    for (int i = values.Count - 1; i >= 0; i--) {
      result = new Cons<T>(values[i], result);
    }
    return result;
  }

  public static SinglyLinkedList<T> Create<T>(params T[] values) {
    return FromList(values);
  }
}

public record Cons<T>(T Head, SinglyLinkedList<T> Tail) : SinglyLinkedList<T> {
  public override IEnumerator<T> GetEnumerator() {
    return new LinkedListEnumerator<T>(this);
  }
}

public record Nil<T>() : SinglyLinkedList<T> {
  public override IEnumerator<T> GetEnumerator() {
    return Enumerable.Empty<T>().GetEnumerator();
  }
}

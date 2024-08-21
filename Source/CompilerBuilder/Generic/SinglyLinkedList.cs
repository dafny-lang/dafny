using System.Collections;

namespace Microsoft.Dafny;

class LinkedListEnumerator<T>(SinglyLinkedList<T> remainder) : IEnumerator<T> {
  private T? current;
  
  public bool MoveNext() {
    return remainder.Fold((head, tail) => {
      current = head;
      remainder = tail;
      return true;
    }, () => false);
  }

  public void Reset() {
    throw new NotSupportedException();
  }

  public T Current => current!;

  object IEnumerator.Current => Current!;

  public void Dispose() {
  }
}

public abstract record SinglyLinkedList<T> : IEnumerable<T> {
  public IEnumerator<T> GetEnumerator() {
    return new LinkedListEnumerator<T>(this);
  }
  
  IEnumerator IEnumerable.GetEnumerator() {
    return GetEnumerator();
  }

  public abstract bool Any();

  public (T, SinglyLinkedList<T>)? ToNullable() {
    return Fold((head, tail) => (head, tail), () => ((T,SinglyLinkedList<T>)?)null);
  }
  
  public abstract U Fold<U>(Func<T, SinglyLinkedList<T>, U> cons, Func<U> nil);
}

public static class LinkedLists {
  public static SinglyLinkedList<T> Concat<T>(SinglyLinkedList<T> left, SinglyLinkedList<T> right) {
    return left.Fold(
      (head, tail) => new Cons<T>(head, Concat<T>(tail, right)), 
      () => right);
  }


  public static SinglyLinkedList<T> FromList<T>(IReadOnlyList<T> values, SinglyLinkedList<T>? tail = null) {
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
  public override bool Any() {
    return true;
  }

  public override U Fold<U>(Func<T, SinglyLinkedList<T>, U> cons, Func<U> nil) {
    return cons(Head, Tail);
  }
}

public record Nil<T> : SinglyLinkedList<T> {
  public override bool Any() {
    return false;
  }

  public override U Fold<U>(Func<T, SinglyLinkedList<T>, U> cons, Func<U> nil) {
    return nil();
  }
}

record LinkedListFromList<T>(IReadOnlyList<T> Source, int Offset = 0) : SinglyLinkedList<T> {
  public override bool Any() {
    return Source.Count > Offset;
  }

  public override U Fold<U>(Func<T, SinglyLinkedList<T>, U> cons, Func<U> nil) {
    if (Source.Count > Offset) {
      return cons(Source[Offset], new LinkedListFromList<T>(Source, Offset + 1));
    }

    return nil();
  }
}

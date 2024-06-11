// This file is translated with AutoExtern

namespace App.Library;

public interface LinkedList<T> {
  public int Length { get; }
}

public class Nil<T> : LinkedList<T> {
  public int Length => 0;
}

public class Cons<T> : LinkedList<T> {
  public T hd;
  public LinkedList<T> tl;

  public int Length => 1 + tl.Length;

  public Cons(T hd, LinkedList<T> tl) {
    this.hd = hd;
    this.tl = tl;
  }
}

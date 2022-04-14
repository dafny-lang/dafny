namespace Library;

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

public class Entry<TItem> {
  public TItem item;
  public int count { get; set; }

  public Entry(TItem item, int count) {
    this.item = item;
    this.count = count;
  }
}

public class GroceryList<TItem> {
  public LinkedList<Entry<TItem>> items { get; init; }

  public GroceryList(LinkedList<Entry<TItem>> items) {
    this.items = items;
  }
}

public enum Fruit { Apple, Pear };

namespace Library;

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

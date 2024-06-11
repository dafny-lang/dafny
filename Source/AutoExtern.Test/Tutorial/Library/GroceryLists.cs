// This file is translated with AutoExtern

namespace App.Library;

public class Entry<TItem> {
  public TItem item;
  public int count { get; set; }
  public ExactArithmetic.Decimal price { get; set; }

  public Entry(TItem item, int count, ExactArithmetic.Decimal price) {
    this.item = item;
    this.count = count;
    this.price = price;
  }
}

public class GroceryList<TItem> {
  public LinkedList<Entry<TItem>> items { get; init; }

  public GroceryList(LinkedList<Entry<TItem>> items) {
    this.items = items;
  }
}

public enum Fruit { Apple, Pear };

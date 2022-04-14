// # C#/Dafny interop: C# side
//
// See README.md for details.  This file constructs a C# value and passes it to Dafny.

namespace ClientApp;

using Library;

class Program {
  public static void Main(string[] args) {
    var apples = new Entry<Fruit>(Fruit.Apple, 3);
    var pears  = new Entry<Fruit>(Fruit.Pear,  2);

    var groceryList = new GroceryList<Fruit>(
      new Cons<Entry<Fruit>>(
        apples,
        new Cons<Entry<Fruit>>(
          pears,
          new Nil<Entry<Fruit>>()
        )
      )
    );

    DafnyPrinter.Printer.PrintGroceryList(groceryList);
  }
}

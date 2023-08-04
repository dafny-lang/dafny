// # C#/Dafny interop: C# side
//
// See README.md for details.  This file constructs a C# value and passes it to Dafny.

namespace App.ClientApp;

using App.Library;
using App.ExactArithmetic;

class Program {
  public static void Main(string[] args) {
    var apples = new Entry<Fruit>(Fruit.Apple, 3, new Decimal(1, 0));
    var pears  = new Entry<Fruit>(Fruit.Pear,  2, new Decimal(15, -1));

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

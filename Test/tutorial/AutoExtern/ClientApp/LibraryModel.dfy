/// # C#/Dafny interop: Dafny model template (filled by AutoExtern from ../Library/Library.cs)

include "../../../../Source/AutoExtern/CSharpModel.dfy"

module {:compile false} {:extern "Library"} Library {
  import opened System

  class {:extern} Fruit {
    static const {:extern} Apple: Fruit
    static const {:extern} Pear: Fruit
    function method {:extern} Equals(other: Fruit): bool
  }

  trait {:compile false} {:extern} LinkedList<T> {
    var {:extern "Length"} LinkedList_Length: System.Int32 // interface property
  }

  trait {:compile false} {:extern} Nil<T> extends LinkedList<T> {
    var Length: System.Int32 // property
  }

  trait {:compile false} {:extern} Cons<T> extends LinkedList<T> {
    var hd: T
    var tl: LinkedList<T>
    var Length: System.Int32 // property
  }

  trait {:compile false} {:extern} Entry<TItem> {
    var item: TItem
    var count: System.Int32 // property
  }

  trait {:compile false} {:extern} GroceryList<TItem> {
    var items: LinkedList<Entry<TItem>> // property
  }

}

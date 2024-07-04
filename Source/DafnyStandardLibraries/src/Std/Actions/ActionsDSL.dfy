include "Actions.dfy"

module {:options "--function-syntax:4"} ActionsDSL {

  import opened Std.Actions
  import opened Wrappers

  trait {:termination false} Enumerable<T> {

    method Enumerator() returns (e: Action<(), (), Option<T>, ()>)

  }

  class ConcatEnumerator<T> extends Action<(), (), Option<T>, ()> {
    constructor() {

    }
  }

  datatype SetEnumerable<T> extends Enumerable<T> = SetEnumerable(s: set<T>) {

  }

  datatype Concat<T> extends Enumerable<T> = Concat(left: Enumerable<T>, right: Enumerable<T>) {
    method Enumerator() returns (e: Action<(), (), Option<T>, ()>) {
      return new ConcatEnumerator();
    }
  }


  method Main() {
    var s := Concat(
      SetEnumerable({1, 2, 3}), 
      SetEnumerable({4, 5, 6}));

    // Someday?
    // foreach x <- s {
    //   print x;
    // }

    }
  }
}
// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = Some(value: T) | None {
  predicate method IsFailure() {
    None?
  }
  function method PropagateFailure<U>(): Option<U>
    requires None?
  {
    None
  }
  function method Extract(): T
    requires Some?
  {
    value
  }
}

type State(==)


function method Gimmie(): Option<int>


method Test5(s: State)
{
  // The definitions of x, y, and z are exactly like in Test0
  var x := Some(s);
  var z :=
    var n :- Gimmie();
    Some(100.0);

  var c := x == z;  // ERROR: this should give a type error
}


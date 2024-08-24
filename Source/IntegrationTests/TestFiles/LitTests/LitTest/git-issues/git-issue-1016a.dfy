// RUN: %exits-with 2 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Option<T> = Some(value: T) | None {
  predicate IsFailure() {
    None?
  }
  function PropagateFailure<U>(): Option<U>
    requires None?
  {
    None
  }
  function Extract(): T
    requires Some?
  {
    value
  }
}

type State(==)


function Gimmie(): Option<int>


method Test5(s: State)
{
  // The definitions of x, y, and z are exactly like in Test0
  var x := Some(s);
  var z :=
    var n :- Gimmie();
    Some(100.0);

  var c := x == z;  // ERROR: this (or the literal 100.0 above) should give a type error
}


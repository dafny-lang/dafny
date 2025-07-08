// RUN: %testDafnyForEachResolver "%s"

datatype Option<T> = Some(val: T) | None {
  predicate  IsFailure() {
    None?
  }
  
  function  PropagateFailure<V>(): Option<V>
    requires None?
  {
    None
  }

  function Extract(): T
    requires Some?
  {
    val
  }
}

function Foo0(): Option<bool> {
  var x: Option<bool> :- None;
  None
}

function Foo1(): Option<bool> {
  var x: Option<int> :- None;
  None
}

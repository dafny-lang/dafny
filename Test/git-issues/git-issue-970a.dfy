// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Library {
  datatype Result<T> = Success(value: T) | Failure(error: string)
  {
    predicate method IsFailure() {
      Failure?
    }
    function method PropagateFailure<U>(): Result<U>
      requires Failure?
    {
      Failure(this.error)
    }
    function method Extract(): T
      requires Success?
    {
      value
    }
  }

  function method F(): Result<string>
}

method Test0() {
  var res :- expect Library.F();  // (onced had caused Internal Error)
}

method Test1() {
  var res :- Library.F();  // error: Test1 is expected to have an out-parameter (once had causes crash)
}

method Test2() returns (r: Library.Result<string>) {
  var res :- Library.F();  // (once had causes crash)
}

function method G(): Library.Result<string>

method Test3() {
  var res :- expect G();  // (onced had caused Internal Error)
}

method Test4() {
  var res :- G();  // error: Test1 is expected to have an out-parameter (once had causes crash)
}

method Test5() returns (r: Library.Result<string>) {
  var res :- G();  // (once had causes crash)
}

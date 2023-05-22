// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Library {
  datatype Result<T> = Success(value: T) | Failure(error: string)
  {
    predicate IsFailure() {
      Failure?
    }
    function PropagateFailure<U>(): Result<U>
      requires Failure?
    {
      Failure(this.error)
    }
    function Extract(): T
      requires Success?
    {
      value
    }
  }

  function F(): Result<string>
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

function G(): Library.Result<string>

method Test3() {
  var res :- expect G();  // (onced had caused Internal Error)
}

method Test4() {
  var res :- G();  // error: Test1 is expected to have an out-parameter (once had causes crash)
}

method Test5() returns (r: Library.Result<string>) {
  var res :- G();  // (once had causes crash)
}

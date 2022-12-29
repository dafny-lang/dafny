// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  datatype Result<T> = Failure(msg: string) | Success(value: T) {
    predicate method IsFailure() { Failure? }
    function method PropagateFailure(): Result<T> requires IsFailure() { this }
    method Extract() returns (t: T) requires !IsFailure() ensures t == this.value { return this.value; }
  }

  method mm() returns (rr: Result<int>) {
    var a := new int[10];
    var r := Success(100);
    var k: int;

    a[1], k :- r, 0; // OK
    a[1..2], k :- r, 0; // ERROR
    a[ ..2], k :- r, 0; // ERROR
    a[ .. ], k :- r, 0; // ERROR
    a[1.. ], k :- r, 0; // ERROR
  }
}

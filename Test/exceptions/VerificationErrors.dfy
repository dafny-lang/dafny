// RUN: %dafny "%s" /rprint:"%t.rprint" > "%t"
// RUN: %diff "%s.expect" "%t"

include "./NatOutcome.dfy"
include "./VoidOutcome.dfy"

method CheckThatVerifierRunsInsideDesugaredExprs_Nat(r1: NatOutcome, r2: NatOutcome) returns (res: NatOutcome) {
    var a :- MakeNatSuccess(assert r1 == r2; 12);  // error: assertion violation
    res := MakeNatSuccess(a);
}

method CheckThatVerifierRunsInsideDesugaredExprs_Void(r1: VoidOutcome, r2: VoidOutcome) returns (res: VoidOutcome) {
    var x := assert 2 + 2 == 4; 8;
    assert x == 8;
    :- assert r1 == r2; r1;  // error: assertion violation
    res := r1;
}

// --------------------

module MultiFailures {
  datatype Option<T> = None | Some(get: T) {
    predicate method IsFailure()
    { None? }
    function method Extract(): T
      requires Some?
    { get }

    function method PropagateFailure<U>(): Option<U>
      requires None?
    { None }
    function method PropagateFailureInt(): int
      requires None?
    { -3 }
  }

  method M(x: int) returns (u: Option<int>)
    ensures x < 0 ==> u == None
    ensures 0 <= x ==> u == Some(7)
  {
    var n := if x < 0 then Option<bool>.None else Some(false);
    assert x < 0 ==> n.IsFailure();
    var b :- n;  // this causes a PropagateFailure if n.IsFailure(); otherwise, sets b to false
    assert !b;
    return Some(7);
  }

  method N(x: int) returns (u: int)
    ensures x < 0 ==> u == -3
    ensures 0 <= x ==> u == 10
  {
    var n := if x < 0 then Option<bool>.None else Some(false);
    var b :- n;  // this causes a PropagateFailureInt if n.IsFailure() (which causes "return -3"); otherwise, sets b to false
    assert !b;
    return 10;
  }

  // ----

  class C {
    method Me(x: int) returns (o: Option<real>)
      ensures match o case None => x < 0 case Some(r) => 0 <= x && r == 3.1
    {
      return if x < 0 then None else Some(3.1);
    }
    function method Fe(x: int): Option<real> {
      if x < 0 then None else Some(5.8)
    }
  }

  method P() returns (u: int)
    ensures u == 90
  {
    var c := new C;
    var g :- c.Me(0);
    assert g == 3.1;
    var h :- c.Fe(0);
    assert h == 5.8;
    return 90;
  }

  method Q(x: int) returns (u: int)
    ensures x < 10 ==> u == -3
    ensures 10 <= x ==> u == 90
  {
    var c := new C;
    var g :- c.Me(x);
    assert g == 3.1;
    var h :- c.Fe(x - 10);
    assert h == 5.8;
    return 90;
  }

  method R0(x: int) returns (u: int)
    ensures u == 90
  {
    var c := new C;
    var g :- c.Me(x);  // error: postcondition might fail
    assert g == 3.1;
    return 90;
  }

  method R1(x: int) returns (u: int)
    ensures u == 90
  {
    var c := new C;
    var h :- c.Fe(x);  // error: postcondition might fail
    assert h == 5.8;
    return 90;
  }
}

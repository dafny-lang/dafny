// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  lemma NonNegative(x: nat)
    ensures 0 <= x
  {
  }

  method Test0() {
    var a: seq<nat> := [0];
    var b: seq<int> := [-1];
    var s: seq<nat>;
    if * {
      s := a + b; // error: RHS is a seq<int>, but not a seq<nat>
    } else {
      s := b + a; // error: RHS is a seq<int>, but not a seq<nat>
    }

    NonNegative(s[0]);
    NonNegative(s[1]);
    assert 0 <= -1;
    assert false;
  }

  method Test1() {
    NonNegative(([0 as nat] + [-1 as int])[1]); // error: argument to NonNegative is not a "nat"
    assert false;
  }

  method Test2() {
    var v: nat := ([0 as nat] + [-1 as int])[1]; // error: argument to NonNegative is not a "nat"
    assert v == -1;
    assert v >= 0;
  }

  function Id<T>(t: T): T { t }

  method Test3() {
    var v := Id<seq<nat>>(Id<seq<nat>>([0]) + Id<seq<int>>([-1]))[1]; // error: wrong type arg to Id<seq<nat>>
    assert false;
  }

  method Test4() {
    var s1: seq<nat> := [0];
    var s: seq<int> := [-1];
    var s1or0: seq<nat> := s1 + s; // error: RHS is not a seq<nat>
    NonNegative(s1or0[0]);
    NonNegative(s1or0[1]);
    assert -1 >= 0;
    assert false;
  }
}

module M1 {
  type int1 = x: int | x == 1 witness 1

  method Needs1(x: int1) {
    print 1 / x;
  }

  method Test0() {
    var s: seq<int> := [0];
    var s1: seq<int1> := [1];
    var s1or0: seq<int1> := s1 + s; // error: RHS is not a seq<int1>
    Needs1(s1or0[1]);
  }

  method Test1() {
    var s: seq<int> := [1, 1];
    var s1: seq<int1> := [1];
    var s1or0: seq<int1> := s1 + s;
    Needs1(s1or0[1]);
  }
}

module M2 {
  type int1 = x: int | x == 1 witness 1
  type int0 = x: int | x == 0 witness 0

  method Needs1(x: int1) {
    print 1 / x;
  }

  method Test0() {
    var s1: seq<int1> := [1];
    var s0: seq<int0> := [0];
    var s1or0: seq<int0> := s1 + s0; // error: RHS is not a seq<int0>
  }

  method Test1() {
    var s1: seq<int1> := [1];
    var s0: seq<int0> := [0];
    var s1or0: seq<int1> := s1 + s0; // error: RHS is not a seq<int1>
    Needs1(s1or0[1]);
  }

  method Test2() {
    var s1: seq<int1> := [1];
    var s0: seq<int0> := [0];
    var s1or0: seq<int> := s1 + s0;
    Needs1(s1or0[1]); // error: argument is not an "int1"
  }

  method Test3() {
    var s1: seq<int1> := [1];
    var s0: seq<int0> := [0];
    var s1or0: seq<int> := s1 + s0;
    Needs1(s1or0[0]);
  }

  method Test4() {
    var s1: seq<int1> := [1];
    var s0: seq<int0> := [0];
    var s1or0 := s1 + s0;
    Needs1(s1or0[0]);
  }
}

module M3 {
  type MyBool = b | !b
  type MyChar = ch | ch == 'D'
  type MyInt = i | i < 17
  type MyReal = r | r == 3.14 || r == 1.618 witness 3.14

  newtype NewTypeInt = i | 0 <= i < 100
  newtype NewTypeReal = r | 0.0 <= r < 100.0
  type MyNewTypeInt = n: NewTypeInt | 2 <= n witness 28
  type MyNewTypeReal = n: NewTypeReal | 2.0 <= n witness 28.9

  type MyBv10 = v: bv10 | v != 7
  type MyOrdinal = o: ORDINAL | 1000 <= o < 1200 witness 1001

  method TestBool(x0: bool, x1: MyBool) {
    var s0: multiset<bool> := multiset{x0};
    var s1: multiset<MyBool> := multiset{x1};
    if
    case true => var a: multiset<bool> := s0 + s1;
    case true => var a: multiset<bool> := s1 + s0;
    case true => var a: multiset<MyBool> := s0 + s1; // error: subset constraint violated
    case true => var a: multiset<MyBool> := s1 + s0; // error: subset constraint violated
    case true => var a := s0 + s1;
    case true => var a := s1 + s0;
  }

  method TestChar(x0: char, x1: MyChar) {
    var s0: multiset<char> := multiset{x0};
    var s1: multiset<MyChar> := multiset{x1};
    if
    case true => var a: multiset<char> := s0 + s1;
    case true => var a: multiset<char> := s1 + s0;
    case true => var a: multiset<MyChar> := s0 + s1; // error: subset constraint violated
    case true => var a: multiset<MyChar> := s1 + s0; // error: subset constraint violated
    case true => var a := s0 + s1;
    case true => var a := s1 + s0;
  }

  method TestInt(x0: int, x1: MyInt) {
    var s0: multiset<int> := multiset{x0};
    var s1: multiset<MyInt> := multiset{x1};
    if
    case true => var a: multiset<int> := s0 + s1;
    case true => var a: multiset<int> := s1 + s0;
    case true => var a: multiset<MyInt> := s0 + s1; // error: subset constraint violated
    case true => var a: multiset<MyInt> := s1 + s0; // error: subset constraint violated
    case true => var a := s0 + s1;
    case true => var a := s1 + s0;
  }

  method TestReal(x0: real, x1: MyReal) {
    var s0: multiset<real> := multiset{x0};
    var s1: multiset<MyReal> := multiset{x1};
    if
    case true => var a: multiset<real> := s0 + s1;
    case true => var a: multiset<real> := s1 + s0;
    case true => var a: multiset<MyReal> := s0 + s1; // error: subset constraint violated
    case true => var a: multiset<MyReal> := s1 + s0; // error: subset constraint violated
    case true => var a := s0 + s1;
    case true => var a := s1 + s0;
  }

  method TestMyNewTypeInt(x0: NewTypeInt, x1: MyNewTypeInt) {
    var s0: multiset<NewTypeInt> := multiset{x0};
    var s1: multiset<MyNewTypeInt> := multiset{x1};
    if
    case true => var a: multiset<NewTypeInt> := s0 + s1;
    case true => var a: multiset<NewTypeInt> := s1 + s0;
    case true => var a: multiset<MyNewTypeInt> := s0 + s1; // error: subset constraint violated
    case true => var a: multiset<MyNewTypeInt> := s1 + s0; // error: subset constraint violated
    case true => var a := s0 + s1;
    case true => var a := s1 + s0;
  }

  method TestNewTypeReal(x0: NewTypeReal, x1: MyNewTypeReal) {
    var s0: multiset<NewTypeReal> := multiset{x0};
    var s1: multiset<MyNewTypeReal> := multiset{x1};
    if
    case true => var a: multiset<NewTypeReal> := s0 + s1;
    case true => var a: multiset<NewTypeReal> := s1 + s0;
    case true => var a: multiset<MyNewTypeReal> := s0 + s1; // error: subset constraint violated
    case true => var a: multiset<MyNewTypeReal> := s1 + s0; // error: subset constraint violated
    case true => var a := s0 + s1;
    case true => var a := s1 + s0;
  }

  method TestBv10(x0: bv10, x1: MyBv10) {
    var s0: multiset<bv10> := multiset{x0};
    var s1: multiset<MyBv10> := multiset{x1};
    if
    case true => var a: multiset<bv10> := s0 + s1;
    case true => var a: multiset<bv10> := s1 + s0;
    case true => var a: multiset<MyBv10> := s0 + s1; // error: subset constraint violated
    case true => var a: multiset<MyBv10> := s1 + s0; // error: subset constraint violated
    case true => var a := s0 + s1;
    case true => var a := s1 + s0;
  }

  method TestOrdinal(x0: ORDINAL, x1: MyOrdinal) {
    var s0: ORDINAL := x0;
    var s1: MyOrdinal := x1;
    if
    case true => var a: ORDINAL := s0 + s1;
    case true => var a: ORDINAL := s1 + s0;
    case true => var a: MyOrdinal := s0 + s1; // error: subset constraint violated
    case true => var a: MyOrdinal := s1 + s0; // error: subset constraint violated
    case true => var a := s0 + s1;
    case true => var a := s1 + s0;
  }
}

module ReferenceTypes {
  datatype Result<U> = Success(value: U) | Failure(exn: Exception)

  trait Exception {
    const message: string
  }

  trait RuntimeException extends Exception {}

  trait IllegalArgumentException extends RuntimeException {}

  function method F(): Result<int>

  function method Test0(): int {
    var x := F();
    match x {
      case Failure(e) =>
        // The following line once reported "type test ... must be from an expression assignable to it (got 'Exception?')"
        if e is IllegalArgumentException then 2 else 3
      case _ => 4
    }
  }

  function method Test1(): int {
    var x := F();
    match x {
      case Failure(e: Exception) =>
        // Even with the explicit type in the previous line, the following line once reported the same error as in Test0
        if e is IllegalArgumentException then 2 else 3
      case _ => 4
    }
  }

  function method Test2(): int {
    var x := F();
    match x {
      case Failure(e) =>
        var e: Exception := e;
        if e is IllegalArgumentException then 2 else 3
      case _ => 4
    }
  }
}

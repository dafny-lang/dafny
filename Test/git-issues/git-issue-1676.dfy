// RUN: %dafny /compile:0 "%s" > "%t"
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

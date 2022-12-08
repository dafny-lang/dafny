// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that datatype updates have the correct return type.

module A {
  type T
  datatype BaseType = BaseType(t: T)

  predicate P(d: BaseType)
  type SubsetType = d: BaseType | P(d) witness *

  method m0(dp: SubsetType)

  method m1(dp: SubsetType, t: T) {
    var dp': SubsetType := [dp][0].(t := t); // Error: `t` does not satisfy subtype constraints
  }
}

module B {
  type R = r: R_ | r.i() witness *

  datatype R_ = R(v: nat) {
    predicate i() { v == 0 }
  }

  datatype S = S(rep: map<nat, R>) {
    function launder(r: R) : R { r }

    function cpy(r: nat, v: nat): R
      requires r in rep
    {
      launder(rep[r].(v := v)) // Error: `v` does not satisfy subtype constraints
    }

    static method bad() ensures false {
      ghost var s := S(map[0 := R(0)]).cpy(0, 1);
      assert s.v == 1;
    }
  }
}

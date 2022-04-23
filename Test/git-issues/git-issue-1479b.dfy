// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type R = r: R_ | r.i() witness *

datatype R_ = R(v: nat) {
  predicate i() { v == 0 }
}

datatype S = S(rep: map<nat, R>) {
  function launder(r: R) : R { r }

  function cpy(r: nat, v: nat): R
    requires r in rep
  {
    launder(rep[r].(v := v))
  }

  static method bad() ensures false {
    ghost var s := S(map[0 := R(0)]).cpy(0, 1);
    assert s.v == 1;
  }
}

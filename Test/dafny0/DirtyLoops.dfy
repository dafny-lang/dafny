// RUN: %dafny /compile:0 /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %dafny /noVerify /compile:1 "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

class MyClass {
  method M0(S: set<int>) {
    forall s | s in S ensures s < 0;
  }

  method M1(x: int)
  {
    var i := x;
    while (0 < i)
      invariant i <= x;
  }

  method M2(x: int)
  {
    var i := x;
    while (0 < i)
      invariant i <= x;
      decreases i;
  }

  var f: int;

  method M3(x: int)
    requires f <= x;
    modifies `f;
  {
    while (0 < f)
      invariant f <= x;
      decreases f;
      modifies `f;
  }

  predicate P(y: int)
    
  method M4() {
    forall y: int  // this once used to crash Dafny
      ensures P(y)

    forall x: int  // this once used to crash Dafny
  }
}

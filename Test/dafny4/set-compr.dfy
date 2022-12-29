// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  method M()
    modifies set o: object | allocated(o)  // allowed, since comprehension is in ghost context
  {
  }

  method N()
    requires null in set o: object? | allocated(o)  // (X) allowed, since comprehension is in ghost context
    ensures null in set o: object? | allocated(o)  // (X) allowed, since comprehension is in ghost context
    decreases set o: object | allocated(o)  // (X) allowed, since comprehension is in ghost context
  {
    N();
  }

  method O() returns (ghost p: set<object>)
  {
    assert null in set o: object? | allocated(o);  // (X) allowed -- in a ghost context
    p := set o: object | allocated(o);  // (X) allowed -- in a ghost context
  }
}

module Compilable {
  method P() returns (p: set<object>)
  {
    p := set o: object | allocated(o);  // error: not (easily) compilable
  }
}

module M1 {
  ghost method Q() returns (p: set<object>)
  {
    p := set o: object | allocated(o);  // allowed, since the whole method is ghost
  }

  function F(p: object): int
    requires p in set o: object | allocated(o)  // error: function is not allowed to depend on allocation state
    ensures p in set o: object | allocated(o)  // error: ditto (although one could argue that this would be okay)
    reads set o: object | allocated(o)  // error: same as for 'requires'
    decreases set o: object | allocated(o)  // error: same as for 'ensures'
  {
    if p in set o: object | allocated(o) then  // error: function is not allowed to depend on allocation state
      F(p)
    else
      0
  }

  function method G(p: object): int
    requires p in set o: object | allocated(o)  // error (see F)
    ensures p in set o: object | allocated(o)  // error (see F)
    reads set o: object | allocated(o)  // error (see F)
    decreases set o: object | allocated(o)  // error (see F)
  {
    if p in set o: object | allocated(o) then  // error (see F)
      G(p)
    else
      0
  }
}

module M2 {
  function method G(p: object): int

  method M0() returns (ghost r: int, s: int)
    requires null in set o: object? | allocated(o)  // allowed
    ensures null in set o: object? | allocated(o)  // allowed
    modifies set o: object | allocated(o)  // allowed
    decreases set o: object | allocated(o)  // allowed
  {
    if null in set o: object? | allocated(o) {  // this makes the "if" a ghost
      r := G(null);
      s := G(null);  // error: assignment of non-ghost not allowed inside ghost "if"
    } else {
      r := 0;
    }
  }

  method M1() returns (ghost r: int, s: int)
    requires null in set o: object? | allocated(o)  // (X) allowed
    ensures null in set o: object? | allocated(o)  // (X) allowed
    modifies set o: object | allocated(o)  // allowed
    decreases set o: object | allocated(o)  // (X) allowed
  {
    if null in set o: object? | allocated(o) {  // this makes the "if" a ghost
      r := G(null);
      s := G(null);  // error: assignment of non-ghost not allowed inside ghost "if"
    } else {
      r := 0;
    }
  }
}

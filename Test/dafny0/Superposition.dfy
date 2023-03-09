// RUN: %exits-with 4 %dafny /compile:0 /tracePOs /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M0 {
  class C {
    method M(c: C?, x: int, y: int) returns (r: int)
      requires 0 <= x && 0 <= y;
      ensures r < 100;
    {
      if (c == null) {
        assert c == null;
      } else if (*) {
        assert 0 <= x;
      } else {
        assert 0 <= y;
      }
      r := 8;
    }

    ghost predicate Q(x: int)
      ensures Q(x) ==> x < 60;  // error: postcondition violation
    {
      true
    }

    ghost predicate R(x: int)
      ensures R(x) ==> x < 60;  // error: postcondition violation
    {
      true
    }
  }
}

module M1 refines M0 {
  class C ... {
    method M...  // no further proof obligations for M, which is just making M0.M more deterministic
    {
      if ... {}
      else if (x == y) {}
      else {}
    }

    ghost predicate Q...  // we don't want another error about Q's body here (because it should not be re-checked here)
    // Ditto for R
  }
}

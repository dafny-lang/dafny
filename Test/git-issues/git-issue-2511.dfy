// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module WhileLoops {
  lemma false_lemma()
    ensures false
  {
    var tmp: bv64 := 1;
    while tmp != 0
      decreases tmp
    {
      tmp := tmp >> 1;
    }
    assert false; // Assertion failure
  }
}

module Recursion {
  method Infloop(b: bv8)
    requires b == 3
    ensures false
    decreases b
  {
    Infloop'(b + 1); // decreases clause might not decrease
  }

  method Infloop'(b: bv8)
    requires b == 4
    decreases b, 0
    ensures false
  {
    Infloop(b - 1);
  }

  method Boom()
    ensures false
  {
    Infloop(3);
  }
}

module Traits {
  trait T {
    method Infloop(b: bv8)
      requires b == 3
      ensures false
      decreases b
  }

  class C extends T {
    method Infloop(b: bv8) // method's decreases clause must be below or equal to that in the trait
      requires b == 3
      ensures false
      decreases b + 1, 0
    {
      (this as T).Infloop(b);
    }
  }
}

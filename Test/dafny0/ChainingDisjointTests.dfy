// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module TestDisjointSets {
  method testing1()
  {
     var a, b, c := {1,2}, {3, 4}, {5, 6};
     assert a !! b !! c;
     testing2(a, b, c);
     assert !({1,2} !! {2,3});
     assert !({1,2} !! {9} !! {2,3}); // tests the accumulation
     assert !({1,2} !! {9} !! {2,3});
     assert !({1,2} !! {9} !! {8} !! {2,3}); // doesn't break at 4. that seems like a good stopping place.
     assert !({9} !! {1,2} !! {8} !! {2,3});
     assert !({9} !! {1} + {2} !! {8} !! {2,3}); // mixing in some other operators
     assert !({1} !! {1} + {2});
  }

  method testing2(a: set<int>, b: set<int>, c: set<int>)
     requires a !! b !! c;
  {
     assert a !! b;
     assert a !! c;
     assert b !! c;
  }

  method testing3(a: set<int>, b: set<int>, c: set<int>, d: set<int>) // again with the four.
     requires a !! b !! c !! d;
  {
     assert a !! b;
     assert a !! c;
     assert b !! c;
     assert a !! d;
     assert b !! d;
     assert c !! d;
  }
}  // module TestDisjointSets

// -------------------------

module TestTernary {
  codatatype Stream = SCons(x: int, Stream)

  lemma TestChainK(s: Stream, t: Stream, u: Stream, k: nat)
    requires s ==#[k] t
    // Regression test:  once upon a time, a bug in Dafny dropped any part of a chain
    // left of a ==#[k] or !=#[k].  The following assertion tests that it is included.
    ensures u ==#[k] s ==#[k] t;  // error: the first part of the chain does not hold: "u ==#[k] s"
  {
  }
}  // module TestTernary

// -------------------------

module TestLocations {
  method LocationTest(a: int, b: int, c: int, d: int)
  {
    assert a == b <= c < d;  // error (x3)
  }
} // module XYZ

// -------------------------

module TestTypeInference {
  datatype List<T> = Nil | Cons(T, List)
  method M(xs: List<int>)
    requires xs == List.Nil == List.Nil  // once upon a time, the second chained equality failed type inference
  {
  }
}

// -------------------------

module TestTypeInferenceExports {
  export reveals List provides M
  datatype List<T> = Nil | Cons(T, List)
  method M(xs: List<int>)
    requires xs == List.Nil == List.Nil  // once upon a time, the second chained equality failed type inference
  {
  }
}

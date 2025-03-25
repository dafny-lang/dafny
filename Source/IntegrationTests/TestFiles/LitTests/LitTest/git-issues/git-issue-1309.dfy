// RUN: %exits-with 2 %verify --allow-axioms "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Example for Issue 1309 -- not yet fixed

module A {
  module C {
    datatype Option<T> = None | Some(x : T)
  }
}

module B {
  module C {
    datatype Option<T> = None | Some(x : T)
  }
}

module D {
  import A
  import B

  lemma Bad(x: int)
    ensures A.C.Some(x) == B.C.Some(x) // error, but gives a confusing error message
}


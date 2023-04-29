// RUN: %exits-with 2 %baredafny verify --use-basename-for-filename "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
  ensures A.C.Some(x) == B.C.Some(x)
}


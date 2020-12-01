// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  datatype T = T(i: int)
  type X
}

module B {
  import A
  type T = A.T
  type K
}

module C {
  import A
  type T = A.T
  type K
  type X = A.X
}

module D {
  import opened B
  import opened C

  function f(t: T) : T { t } // OK. B.T and C.T are both A.T
  function g(k: K) : K { k } // Error: ambiguous

}

module E {
  import opened A
  import opened C

  function g(x: X) : X { x }  // OK - A.X and C.X are the same
}

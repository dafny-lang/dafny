// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Z {
  datatype T = T(i: int)
  type X
  ghost function z(): int { 0 }
  const c := 10;
}

module B {
  import A = Z
  type T = A.T
  type K
}

module C {
  import A = Z
  type T = A.T
  type K
  type X = A.X
}

module D {
  import opened B
  import opened C

  ghost function f(t: T) : T { t } // OK. B.T and C.T are both A.T
  ghost function g(k: K) : K { k } // Error: ambiguous
  ghost function h(): int { z() }
  const d := c;
}

module E {
  import opened A = Z
  import opened CC = C

  method g(x: X) {}  // OK - Z.X and C.X are the same
  ghost function h(): int { z() }
  const d := c;
}

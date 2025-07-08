// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module A {
  type T = int
  type U = int
  type V = int
  type W = int
  type X = x: int | x > -10
  type Y = x: int | x > -10
  newtype Z = int
  newtype K = int
}

module B {
  type U = real
  type V = int
  type W = nat
  type X = x: int | x > -10
  newtype Z = int
}

module D {
  import A
  type Y = A.Y
  type K = A.K
}

module C {
  import opened A
  import opened B
  import opened D

  type T = A.T

  function Baz(x: T): T { 0 } // OK C.T is local
  function Bar(x: U): U { 0 } // Error A.U, B.U conflict
  function Bam(x: V): V { 0 } // OK A.V, B.V are the same type
  function Baa(x: W): W { 0 } // Error A.W, B.W are different
  function Bag(x: X): X { 0 } // Error A.X, B.X are different
  function Bay(x: Y): Y { 0 } // OK A.Y, D.Y are the same type
  function Bat(x: Z): Z { 0 } // Error: A.Z, B.Z are different newtypes
  function Ban(x: K): K { 0 } // OK: A.K, D.K refer to same decl
}

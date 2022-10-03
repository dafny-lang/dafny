// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Opaque

class A<T> {

  constructor()

}

datatype B = B(A<Opaque>)

type C(==) = B

trait D<T> {}

datatype E = E(D<Opaque>)

type F(==) = E

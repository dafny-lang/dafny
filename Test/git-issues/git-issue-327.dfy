// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
}

module B {
  import A
}

module C0 {}

module C refines C0 {
  import B
}

module CC refines C {}

module D refines CC {
  import A = B.A
}

module E {
  import A
}

module F {
  import E
  import E.A
}

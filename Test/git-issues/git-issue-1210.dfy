// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module A {
  const c: nat
}
abstract module B refines A {}
module C refines B {
  const c: nat := 0
}

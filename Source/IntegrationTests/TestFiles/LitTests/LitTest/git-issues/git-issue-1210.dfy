// RUN: %testDafnyForEachResolver "%s"


abstract module A {
  const c: nat
}
abstract module B refines A {}
module C refines B {
  const c: nat := 0
}

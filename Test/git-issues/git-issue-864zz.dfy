// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export reveals a
  const a := 10
  const b := 20
}

module B refines A {
  export X reveals * extends A // used to complain  A is not in B
}

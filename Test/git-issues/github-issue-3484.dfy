// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Foo(x: int) {
  match x {

  }
}

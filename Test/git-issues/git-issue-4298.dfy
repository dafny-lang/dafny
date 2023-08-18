// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export E
    provides f

  function f() : bool { true }
}

abstract module B {
  import A0: A
}
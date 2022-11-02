// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module StillAsby {
  import A : Absy

}

abstract module Absy {
  method Foo() 
    ensures 2 / 0 == 1 {
    var x := 1;
  }
}
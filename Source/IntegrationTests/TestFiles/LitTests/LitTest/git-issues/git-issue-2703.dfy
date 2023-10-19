// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
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

abstract module Absy2 {
  ghost function f(): int { 0 / 0 }
}

abstract module StillAsby2 refines Absy2 {
}

abstract module Absy3 {
  ghost function f(): int { 0 / 0 }
}

abstract module StillAsby3 {
  import A: Absy3
}
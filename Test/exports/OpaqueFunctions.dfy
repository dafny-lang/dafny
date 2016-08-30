// RUN: %dafny /env:0 /dprint:"%t.dfy" /compile:0 "%s" > "%t.result"
// RUN: %diff "%s.expect" "%t.result"

module A {
  export A provides f
  export B reveals f
  function f() : nat { 7 }

}

module B {
  import A = A`A

  function g() : nat { A.f() }

  function h() : nat
  ensures h() == 7
  { g() } // error

}

module C {
  import A = A`B

  function g() : nat { A.f() }

  function h() : nat
  ensures h() == 7
  { g() }

}

module D {
  import A = A`A 
  function g() : nat { A.f() }
}

module E {
  import D
  import A`B
  
  function h() : nat
  ensures h() == 7
  { D.g() } // revealed via A`B

}

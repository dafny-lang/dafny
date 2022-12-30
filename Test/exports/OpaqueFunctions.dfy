// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

module AA {
  export Spec provides f
  export Body reveals f
  function {:opaque} f(): int { 0 }
}

module BB {
  import A = AA`Spec
  lemma Test()
  ensures A.f() == 0 // fails
  { }
}

module CC {
  import A= AA`Body
  lemma Test1()
  ensures A.f() == 0 // fails
  { }

  lemma Test2()
  ensures A.f() == 0
  { reveal A.f(); }
}

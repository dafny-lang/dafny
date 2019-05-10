// RUN: %dafny /env:0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export fandg provides f, g
  export justf provides f

  function f(): int { 0 }
  function g(): int { 1 }

}

module B {
  import Afandg = A`fandg
  import A : A`justf

  function h(): int { A.f() + Afandg.g() + Afandg.f() }
}

module BB {
  import A : A`justf
  import Afandg = A`fandg

  function h(): int { A.f() + Afandg.g() + Afandg.f() }
}

module C {
  import Afandg = A`fandg
  import A = A`justf

  function h(): int { A.f() + Afandg.g() + Afandg.f() }
}

module CC {
  import A = A`justf
  import Afandg = A`fandg

  function h(): int { A.f() + Afandg.g() + Afandg.f() }
}

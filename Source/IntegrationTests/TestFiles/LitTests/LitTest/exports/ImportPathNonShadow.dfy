// RUN: %dafny /env:0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export fandg provides f, g
  export justf provides f

  ghost function f(): int { 0 }
  ghost function g(): int { 1 }

}

abstract module B {
  import Afandg = A`fandg
  import A : A`justf

  ghost function h(): int { A.f() + Afandg.g() + Afandg.f() }
}

abstract module BB {
  import A : A`justf
  import Afandg = A`fandg

  ghost function h(): int { A.f() + Afandg.g() + Afandg.f() }
}

module C {
  import Afandg = A`fandg
  import A = A`justf

  ghost function h(): int { A.f() + Afandg.g() + Afandg.f() }
}

module CC {
  import A = A`justf
  import Afandg = A`fandg

  ghost function h(): int { A.f() + Afandg.g() + Afandg.f() }
}

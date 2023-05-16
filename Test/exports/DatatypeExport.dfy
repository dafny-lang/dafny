// RUN: %exits-with 2 %dafny /env:0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
 export Spec provides T, f
 export Body provides f reveals T

 datatype T = CT1 | CT2 (X: int)

 ghost function f(): T { CT1 }
}

module B {
  import A`Spec

  ghost function g(): A.T { A.f() }
}

module C {
  import A`Body
  import B

  ghost function g(): A.T { A.CT1 }

  ghost function h(x : A.T): int {
    match x
      case CT1 => 0
      case CT2(n) => n
  }
  ghost function k(x : A.T): int { if x.CT1? then 1 else x.X }
  ghost function i(): int {
    match B.g()
       case CT1 => 0
       case CT2(n) => n
  }
}

module CBad {
  import A`Spec

  ghost function g(): A.T { A.CT1 } //can't construct one

  ghost function h(x : A.T): int {
    match x //can't match
      case CT1 => 0
      case CT2(n) => n //constructor not resolved, so error here
  }
  ghost function k(x : A.T): int { if x.CT1? then 1 else x.X } // can't access destructors
}


module CIndirect {
  import ABody = A`Body
  import A = A`Spec

  ghost function g(): A.T { A.CT1 } //error

  ghost function i() : A.T { ABody.CT1 }

  ghost function h(x : A.T): int {
    match x
      case CT1 => 0
      case CT2(n) => n
  }
  ghost function k(x : A.T): int { if x.CT1? then 1 else x.X }
}



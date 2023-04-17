// RUN: %exits-with 2 %dafny /env:0 /dprint:"%t.dfy" /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A{
  export provides T
  export Spec provides f,T

  type T = int
  ghost function f(): T { 0 }

}

module B {
  import opened A`Spec

  export Body provides A reveals g,h
  ghost function g(): T { f() }
  ghost function h(): A.T { f() }
}

module BBad {
  import opened A`Spec

  export Body reveals g,h // we need A
  ghost function g(): T { f() }
  ghost function h(): A.T { f() }
}

module C {
  import opened B`Body
  import AA = A //imports must be qualified, here A refers to the default export of the module A

  ghost function h(): AA.T { AA.f() } // error, AA is A's default export, which does not give f
  ghost function i(): A.T { A.f() } // qualification is fine
  ghost function j(): A.T { f() } // not okay, we don't import openness

}

// RUN: %dafny /env:0 /dprint:"%t.dfy" /compile:0 "%s" > "%t.result"
// RUN: %diff "%s.expect" "%t.result"


abstract module A {
  export Spec provides f, T
  export Body reveals f, T
  type T
  function f(): T
}

module B refines A {
  type T = int
  function f(): T { 0 }
}

abstract module C {
  export Body provides AF reveals g

  import AF : A`Spec

  function g(): AF.T
}

module DBBody refines C {
  import AF = B`Body

  function g(): AF.T { 0 }

}

module DBSpec refines C {
  import AF = B`Spec

  function g(): AF.T { AF.f() }

}

module E {
  import D = DBBody`Body

  function h(): int { D.g() }
}

module F {
  import D = DBSpec`Body

  function h(): int { D.g() } //error
}

//Extending existing exports

module A2 refines A {
  export Spec reveals T

  type T = int
}

module B2 {
  import A2`Spec

  function g(): int { A2.f() }
}

//Facades only must respect the visible export

module C2 {
  import BB : B`Spec
}

module BAlt refines A {
  type T = bool
  function f(): T { false }

}

module C3 refines C2 {
  import BB = BAlt`Spec
}

module C4 refines C2 {
  import BB = BAlt`Body
}

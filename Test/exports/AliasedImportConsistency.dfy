// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


module A {
  export Spec provides T
  export Body reveals T

  type T = int

}

module B {
  export GoodSpec provides f, ASpec
  export AnotherGoodSpec provides f, ABody
  export YetAnotherGoodSpec provides f, ABody, ASpec
  export GoodBody reveals f provides ABody

  import ASpec = A`Spec
  import ABody = A`Body

  function f(): ABody.T { 0 }

}

module C {
  module InnerC {
     export Spec provides T
     export Body reveals T

     type T = nat
  }

  import ASpec = InnerC`Spec
  import ABody = InnerC`Body

  export provides ASpec, ABody

}

module D {
  import C

  import ASpec = C.ASpec
  import ABody = C.ABody

  export provides ASpec, ABody

}

module E {
  import C
  import D

  import CASpec = C.ASpec
  import CABody = C.ABody
  import DASpec = D.ASpec
  import DABody = D.ABody

  export Spec provides f, CASpec
  export AnotherSpec provides f,g, CASpec

  export Body reveals f,g provides CABody
  export AnotherBody reveals f,g provides DABody

  function f(): CABody.T { 0 }
  function g(): DABody.T { f() }

}


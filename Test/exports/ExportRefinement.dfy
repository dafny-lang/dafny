// RUN: %dafny /env:0 /compile:3 /dprint:"%t.dfy" "%s" > "%t.result"
// RUN: %dafny /env:0 /printMode:DllEmbed /dprint:"%t1.dfy" "%t.dfy"
// RUN: %dafny /env:0 /printMode:DllEmbed /dprint:"%t2.dfy" /compile:3 "%t1.dfy" > "%t"
// RUN: %diff "%t1.dfy" "%t2.dfy"
// RUN: %diff "%s.expect" "%t"

abstract module A {
  export Spec provides f, T, m, C
  export Body provides m reveals f, T, C
  type T
  ghost function f(): T
  method m()

  class C {
    method m()
  }
}

module B refines A {
  type T = int
  ghost function f(): T { 0 }
  method m() { print "B\n"; }

  class C ... {
     method m() { print "B.C.m\n"; }
     method n() { print "B.C.n\n"; }
  }
}

abstract module C {
  export Body provides AF reveals g

  import AF : A`Spec

  ghost function g(): AF.T
}

module DBBody refines C {
  import AF = B`{Body,Spec}

  ghost function g(): AF.T { 0 }

}

module DBSpec refines C {
  import AF = B`Spec

  ghost function g(): AF.T { AF.f() }

}

module E {
  import D = DBBody`Body

  ghost function h(): int { D.g() }
}

module F {
  import D = DBSpec`Body

  ghost function h(): D.AF.T { D.g() }
}

//Extending existing exports

module A2 refines A {
  export Spec ... provides m reveals T
  export Body ... extends Spec provides C, C.m, C.Init

  type T = int
  ghost function f(): T { 0 }
  method m() { print "A2\n"; }

  class C ... {
    method m() { print "A2.C.m\n"; }
    method n() { print "A2.C.n\n"; }
    constructor Init() { }
  }
}

module B2 {
  import A2`Spec

  ghost function g(): int { A2.f() }
  method m() { print "B2.m()\n"; A2.m(); }
}

//Facades must be refined by a base module

abstract module C2 {
  import ASpec : A`Spec
}

module C3 refines C2 {
  import ASpec = A2`{Spec,Body}
}

method Main(){
  C3.ASpec.m();
  B2.m();
  var c := new C3.ASpec.C.Init();
  c.m();
}

// ---------- regressions -------------

abstract module Regression_A {
  export Spec provides x
  export Body reveals x
  const x: int := 80
}

abstract module Regression_B {
  // once upon a time, merging two export sets of an abstract module caused a crash
  import Regression_A`{Body,Spec}
}

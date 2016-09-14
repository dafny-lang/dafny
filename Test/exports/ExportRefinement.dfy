// RUN: %dafny /env:0 /compile:3 /dprint:"%t.dfy" "%s" > "%t.result"
// RUN: %dafny /env:0 /printMode:DllEmbed /dprint:"%t1.dfy" "%t.dfy"
// RUN: %dafny /env:0 /printMode:DllEmbed /dprint:"%t2.dfy" /compile:3 "%t1.dfy" > "%t.output"
// RUN: %diff "%t1.dfy" "%t2.dfy"
// RUN: %diff "%s.expect" "%t.output"

abstract module A {
  export Spec provides f, T, m, C
  export Body provides m reveals f, T, C
  type T
  function f(): T
  method m()

  class C {
    method m()
  }
}

module B refines A {
  type T = int
  function f(): T { 0 }
  method m() { print "B\n"; }

  class C {
     method m() { print "B.C.m\n"; }
     method n() { print "B.C.n\n"; }
  }
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

  function h(): D.AF.T { D.g() }
}

//Extending existing exports

module A2 refines A {
  export Spec provides m reveals T

  type T = int
  function f(): T { 0 }
  method m() { print "A2\n"; }

  class C {
    method m() { print "A2.C.m\n"; }
    method n() { print "A2.C.n\n"; }
  }
}

module B2 {
  import A2`Spec

  function g(): int { A2.f() }
  method m() { A2.m(); }
}

//Facades only must respect the visible export

module C2 {
  import BB : B`Spec
}

module BAlt refines A {
  export Spec provides C, C.m, C.n
  export Body reveals C

  type T = bool
  function f(): T { false }
  method m() { print "BAlt\n"; }
  
  class C {
    method m() { print "BAlt.C.m\n"; }
    method n() { print "BAlt.C.n\n"; }
    constructor Init() { }
  }
}

module C3 refines C2 {
  import BB = BAlt`Spec
}

module C4 refines C2 {
  import BB = BAlt`Body
}

method Main(){
  C3.BB.m();
  C4.BB.m();
  B2.m();
  C2.BB.m();
  var c := new C3.BB.C.Init();
  c.m();
  c.n();
  
}

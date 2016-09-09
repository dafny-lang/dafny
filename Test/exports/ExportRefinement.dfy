// RUN: %dafny /env:0 /compile:3 "%s" > "%t.result"
// RUN: %diff "%s.expect" "%t.result"


abstract module A {
  export Spec provides f, T, m
  export Body provides m reveals f, T
  type T
  function f(): T
  method m()
}

module B refines A {
  type T = int
  function f(): T { 0 }
  method m() { print "B\n"; }
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
  type T = bool
  function f(): T { false }
  method m() { print "BAlt\n"; }
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

}

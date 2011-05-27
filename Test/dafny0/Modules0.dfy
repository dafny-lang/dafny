module M {
  class T { }
  class U { }
}

module N {
  class T { } // error: duplicate class name
}

module U imports N {  // fine, despite the fact that a class is called U--module names are in their own name space
}

module V imports T {  // error: T is not a module
}

module A imports B, M {
  class Y { }
}

module B imports N, M {
  class X { }
}

module G imports A, M, A, H, B {  // error: cycle in import graph
}

module H imports A, N, I {
}

module I imports J {
}

module J imports G, M {
}

// --------------- calls

module X2 imports X1 {
  class MyClass2 {
    method Down(x1: MyClass1, x0: MyClass0) {
      x1.Down(x0);
    }
    method WayDown(x0: MyClass0, g: ClassG) {
      x0.Down();
      g.T();  // allowed, because this follows import relation
      var t := g.TFunc();  // allowed, because this follows import relation
    }
    method Up() {
    }
    method Somewhere(y: MyClassY) {
      y.M();  // error: does not follow import relation
    }
  }
}

module X1 imports X0 {
  class MyClass1 {
    method Down(x0: MyClass0) {
      x0.Down();
    }
    method Up(x2: MyClass2) {
      x2.Up();  // error: does not follow import relation
    }
  }
}

module X0 {
  class MyClass0 {
    method Down() {
    }
    method Up(x1: MyClass1, x2: MyClass2) {
      x1.Up(x2);  // error: does not follow import relation
    }
  }
}

module YY {
  class MyClassY {
    method M() { }
    method P(g: ClassG) {
      g.T();  // allowed, because this follows import relation
      var t := g.TFunc();  // allowed, because this follows import relation
    }
  }
}

class ClassG {
  method T() { }
  function method TFunc(): int { 10 }
  method V(y: MyClassY) {
    y.M();  // error: does not follow import relation
  }
}

method Ping() {
  Pong();  // allowed: intra-module call
}

method Pong() {
  Ping();  // allowed: intra-module call
}

method ProcG(g: ClassG) {
  g.T();  // allowed: intra-module call
  var t := g.TFunc();  // allowed: intra-module call
}

// ---------------------- some ghost stuff ------------------------

class Ghosty {
  method Caller() {
    var x := 3;
    ghost var y := 3;
    Callee(x, y);  // fine
    Callee(x, x);  // fine
    Callee(y, x);  // error: cannot pass in ghost to a physical formal
    Theorem(x);  // fine
    Theorem(y);  // fine, because it's a ghost method
  }
  method Callee(a: int, ghost b: int) { }
  ghost method Theorem(a: int) { }
}

var SomeField: int;

method SpecialFunctions()
  modifies this;
{
  SomeField := SomeField + 4;
  var a := old(SomeField);  // error: old can only be used in ghost contexts
  var b := fresh(this);  // error: fresh can only be used in ghost contexts
  var c := allocated(this);  // error: allocated can only be used in ghost contexts
  if (fresh(this)) {  // this guard makes the if statement a ghost statement
    ghost var x := old(SomeField);  // this is a ghost context, so it's okay
    ghost var y := allocated(this);  // this is a ghost context, so it's okay
  }
}

// ---------------------- illegal match expressions ---------------

datatype Tree = Nil | Cons(int, Tree, Tree);

function NestedMatch0(tree: Tree): int
{
  match tree
  case Nil => 0
  case Cons(h,l,r) =>
    match tree  // error: cannot match on "tree" again
    case Nil => 0
    case Cons(hh,ll,rr) => hh
}

function NestedMatch1(tree: Tree): int
{
  match tree
  case Nil => 0
  case Cons(h,l,r) =>
    match l
    case Nil => 0
    case Cons(h0,l0,r0) =>
      match r
      case Nil => 0
      case Cons(h1,l1,r1) => h + h0 + h1
}

function NestedMatch2(tree: Tree): int
{
  match tree
  case Nil => 0
  case Cons(h,l,r) =>
    match l
    case Nil => 0
    case Cons(h,l0,tree) =>  // fine to declare another "h" and "tree" here
      match r
      case Nil => 0
      case Cons(h1,l1,r1) => h + h1
}

function NestedMatch3(tree: Tree): int
{
  match tree
  case Nil => 0
  case Cons(h,l,r) =>
    match l
    case Nil => 0
    case Cons(h0,l0,r0) =>
      match l  // error: cannot match on "l" again
      case Nil => 0
      case Cons(h1,l1,r1) => h + h0 + h1
}

// ---------------------- duplicate types within a module

module Wazzup {
  class WazzupA { }
  class WazzupA { }  // error: duplicate type
  datatype WazzupA = W_A_X;  // error: duplicate type
  type WazzupA;  // error: duplicate type

  type WazzupB;
  type WazzupB;  // error: duplicate type
  class WazzupB { }  // error: duplicate type
  datatype WazzupB = W_B_X;  // error: duplicate type
}

// ---------------------- duplicate types across modules

module M {
  class T { }
  class U { }
}

module N {
  class T { }
}

module U imports N {  // fine, despite the fact that a class is called U,
                      // since module names are in their own name space
}

module UU imports N, U, N, N {  // duplicates are allowed
}

module N_left imports N { }
module N_right imports N { }
module Diamond imports N_left, N_right {  // this imports N.T twice, but that's okay
}

module A imports N, M {  // Note, this has the effect of importing two different T's,
                         // but that's okay as long as the module doesn't try to access
                         // one of them
  class X {
    var t: T;  // error: use of the ambiguous name T
    function F(x: T):  // error: use of the ambiguous name T
               T  // error: use of the ambiguous name T
    { x }
    method M(x: T)  // error: use of the ambiguous name T
      returns (y: T)  // error: use of the ambiguous name T
  }
}
module A' imports N, M {
  method M()
    { var g := new T; }  // error: use of the ambiguous name T
}

module B0 imports A {
  class BadUse {
    var b0: T;  // error: T is not directly accessible
  }
}

module B1 imports A, N {
  class GoodUse {
    var b1: T;  // fine
  }
}

// --------------- calls

module X0 {
  class MyClass0 {
    method Down() {
    }
    method Up(x1: MyClass1,  // error: MyClass1 is not in scope
              x2: MyClass2) {  // error: MyClass2 is not in scope
    }
  }
}

module X1 imports X0 {
  class MyClass1 {
    method Down(x0: MyClass0) {
      x0.Down();
    }
    method Up(x2: MyClass2) {  // error: class MyClass2 is not in scope
    }
  }
}

module X2 imports X0, X1, YY {
  class MyClass2 {
    method Down(x1: MyClass1, x0: MyClass0) {
      x1.Down(x0);
    }
    method WayDown(x0: MyClass0) {
      x0.Down();
    }
    method Up() {
    }
    method Somewhere(y: MyClassY) {
      y.M();
    }
  }
}

module YY {
  class MyClassY {
    method M() { }
    method P(g: ClassG) {  // error: ClassG is not in scope
    }
  }
}

class ClassG {
  method T() { }
  function method TFunc(): int { 10 }
  method V(y: MyClassY) {  // Note, MyClassY is in scope, since we are in the _default
                           // module, which imports everything
    y.M();
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

// ---------------------- direct imports are not transitive

module ATr {
  class X {
    method M() returns (q: int)
    {
      q := 16;
    }
    static method Q() returns (q: int)
    {
      q := 18;
    }
  }
}

module BTr imports ATr {
  class Y {
    method N() returns (x: X)
      ensures x != null;
    {
      x := new X;
    }
  }
}

module CTr imports BTr {
  class Z {
    var b: Y;  // fine
    var a: X;  // error: imports don't reach name X explicitly
  }
}
module CTs imports BTr {
  method P() {
    var y := new Y;
    var x := y.N();  // this is allowed and will correctly infer the type of x to
                     // be X, but X could not have been mentioned explicitly
    var q := x.M();
    var r := X.Q();  // error: X is not in scope
    var s := x.DoesNotExist();  // error: method not declared in class X
  }
}

// ---------------------- module-local declarations override imported declarations

module NonLocalA {
  class A {
    method M() { }
  }
  class Common {
    method P() { }
  }
}

module NonLocalB {
  class B {
    method N() { }
  }
  class D {
    method K() returns (b: B)
      ensures b != null;
    {
      return new B;
    }
  }
  class Common {
    method P() { }
  }
}

module Local imports NonLocalA, NonLocalB {
  class MyClass {
    method MyMethod()
    {
      var b := new B;
      var c := new Common;
      var d := new D;
      c.Q();  // this is fine, since c's type is the local class Common
      b.R();  // fine, since B refers to the locally declared class
      var nonLocalB := d.K();
      nonLocalB.N();
      nonLocalB.R();  // error: this is not the local type B
    }
  }
  class B {
    method R() { }
  }
  class Common {
    method Q() { }
  }
}

// ------ qualified type names ----------------------------------

module Q_Imp {
  class Node { }
  datatype List<T> = Nil | Cons(T, List);
  class Klassy {
    method Init()
  }
}

module Q_M imports Q_Imp {
  method MyMethod(root: Q_Imp.Node, S: set<Node>)
    requires root in S;  // error: the element type of S does not agree with the type of root
  {
    var i := new Q_Imp.Node;
    var j := new Node;
    assert i != j;  // error: i and j have different types
    var k: LongLostModule.Node;  // error: undeclared module
    var l: Wazzup.WazzupA;  // error: undeclared module (it has not been imported)
    var m: Q_Imp.Edon;  // error: undeclared class in module Q_Imp
    var n: Q_Imp.List;
    var o := new Q_Imp.List;  // error: not a class declared in module Q_Imp
    var p := new Q_Imp.Klassy.Create();  // error: Create is not a method
    var q := new Q_Imp.Klassy.Init();
  }
  class Node { }
}

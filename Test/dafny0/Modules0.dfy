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
      call x1.Down(x0);
    }
    method WayDown(x0: MyClass0, g: ClassG) {
      call x0.Down();
      call g.T();  // allowed, because this follows import relation
      var t := g.TFunc();  // allowed, because this follows import relation
    }
    method Up() {
    }
    method Somewhere(y: MyClassY) {
      call y.M();  // error: does not follow import relation
    }
  }
}

module X1 imports X0 {
  class MyClass1 {
    method Down(x0: MyClass0) {
      call x0.Down();
    }
    method Up(x2: MyClass2) {
      call x2.Up();  // error: does not follow import relation
    }
  }
}

module X0 {
  class MyClass0 {
    method Down() {
    }
    method Up(x1: MyClass1, x2: MyClass2) {
      call x1.Up(x2);  // error: does not follow import relation
    }
  }
}

module YY {
  class MyClassY {
    method M() { }
    method P(g: ClassG) {
      call g.T();  // allowed, because this follows import relation
      var t := g.TFunc();  // allowed, because this follows import relation
    }
  }
}

class ClassG {
  method T() { }
  function method TFunc(): int { 10 }
  method V(y: MyClassY) {
    call y.M();  // error: does not follow import relation
  }
}

method Ping() {
  call Pong();  // allowed: intra-module call
}

method Pong() {
  call Ping();  // allowed: intra-module call
}

method ProcG(g: ClassG) {
  call g.T();  // allowed: intra-module call
  var t := g.TFunc();  // allowed: intra-module call
}

// ---------------------- some ghost stuff ------------------------

class Ghosty {
  method Caller() {
    var x := 3;
    ghost var y := 3;
    call Callee(x, y);  // fine
    call Callee(x, x);  // fine
    call Callee(y, x);  // error: cannot pass in ghost to a physical formal
    call Theorem(x);  // fine
    call Theorem(y);  // fine, because it's a ghost method
  }
  method Callee(a: int, ghost b: int) { }
  ghost method Theorem(a: int) { }
}

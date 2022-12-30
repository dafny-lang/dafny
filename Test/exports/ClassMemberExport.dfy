// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
   export Spec reveals AClass provides T, AClass.f, AClass.Init
   export Body reveals T, AClass provides AClass.Init, AClass.f, AClass.g

   type T = int
   class AClass {
     function method f(): T { 0 }
     function method g(): int { f() }
     constructor Init() { }
   }
}

module B {
  import A = A`Spec

  method Test() {
    var a := new A.AClass.Init();
    var f : A.T := a.f();
  }

}

module C {
  import A = A`Body

  method Test() {
    var a := new A.AClass.Init();
    var f : int := a.f();
    var g : A.T := a.g();
    var e := f == g;
  }

}

// RUN: %exits-with 4 %dafny /env:0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export Spec reveals AClass provides *  // when class is revealed, "provides *" also provides all the constructors of the class
  export Body reveals *

  datatype T = CT1 | CT2

  ghost function getCT1() : T { CT1 }
  ghost function getCT2() : T { CT2 }

  class AClass {
     function getCT1(): T { CT1 }
     constructor Init() {}
  }

}

module B {
  import A`Spec

  ghost function f(): A.T { A.getCT1() }
  lemma Test(x : A.T)
  ensures x == A.getCT1() || x == A.getCT2() { } //can't prove this here

  method TestClass() {
    var a := new A.AClass.Init();
    var f := a.getCT1();
    assert f == A.getCT1();// can't prove this here
  }
}

module C {
  import A`Body

  ghost function f(): A.T { A.CT1 }

  lemma Test()
  ensures A.CT1 == A.getCT1() { }

  lemma Test2(x : A.T)
  ensures x == A.getCT1() || x == A.getCT2() { }

  method TestClass() {
    var a := new A.AClass.Init();
    var f := a.getCT1();
    assert f == A.getCT1();
  }

}

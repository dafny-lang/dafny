// RUN: %dafny_0 /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  trait {:termination false} Trait {
    function method TotallyNotZero() : (ret: int)
      ensures ret != 0
  }
}

module B {

  import opened A

  class Class extends Trait {
    constructor() {}
    function method TotallyNotZero() : (ret: int)
      // Missing: ensures ret != 0
    { 
      0 
    }
  }

  method Main() {
    var asClass: Class := new Class();
    var asTrait: Trait := asClass;
    assert asClass.TotallyNotZero() == asTrait.TotallyNotZero();
    assert false;
    print 1 / asClass.TotallyNotZero(), "\n";
  }
}
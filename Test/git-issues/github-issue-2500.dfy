module A {
  trait {:termination false} Trait {
    function TotallyNotZero() : (ret: int)
      ensures ret != 0
  }
}

module B {

  import opened A

  class Class extends Trait {
    constructor() {}
    function TotallyNotZero() : (ret: int)
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
  }
}
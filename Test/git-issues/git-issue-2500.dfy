// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
}

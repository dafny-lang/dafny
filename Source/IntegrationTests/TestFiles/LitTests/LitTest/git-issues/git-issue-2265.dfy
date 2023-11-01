// RUN: %testDafnyForEachResolver "%s"


module DefaultModule {
  class DefaultClass {
    static ghost function BrokenFunction(): nat {
      var y := 0;
      assert true by {
        if foobarquux: bool :| true {
          assert true || foobarquux;
        }
      }
      0
    }
  }
}



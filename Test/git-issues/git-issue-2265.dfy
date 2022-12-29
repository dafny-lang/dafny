// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module DefaultModule {
  class DefaultClass {
    static function BrokenFunction(): nat {
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



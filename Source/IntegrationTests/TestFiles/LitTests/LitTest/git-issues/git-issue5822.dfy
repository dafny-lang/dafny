// RUN: ! %testDafnyForEachResolver "%s"

module Issue5822 {
    trait A {
      var x: int
      function Test(): int
        ensures Test() == x
    
      method EnsureFalse() modifies this
        ensures false
      {
        x := 1;
        var i := Test();
        x := 2;
        var j := Test();
      }
    }
}
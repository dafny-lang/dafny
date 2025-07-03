// RUN: ! %verify %s > %t
// RUN: %diff "%s.expect" "%t"
 
trait T {
  method foo() returns (r: int)  
    ensures r >= 3
  {
    return 3;
  }
}

trait Bad extends T {
  method foo() returns (r: int)  
    ensures r >= 1
  {
    return 4;
  }
}

class Better extends Bad {
  method foo() returns (r: int)  
    ensures r >= 2
  {
    return 4;
  }
}

method useBetter(better: Better) {
  var r := better.foo();
  assert r >= 2;
}

// Termination

trait Termination extends object {
  method M() {
    if this is Termination {
      var c := this as Termination;
      c.M(); // error: cannot prove termination
    }
  }
  method N() {
  }
}

class CTermination extends Termination {
  method M() {
    var t := this as Termination;
    t.M(); // error: cannot prove termination
  }
  method N() {
    var t := this as Termination;
    t.N(); // error: cannot prove termination
  }
}
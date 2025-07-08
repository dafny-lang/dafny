// RUN: %exits-with 2 %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Type errors from Issue 5726 (see also git-issue-5726b.dfy)

module Example0 {
  trait G {
    const Three := 3
    const Six := Three + Three
  }

  class E extends G { }

  method DoIt<G1 extends G>(g1: G1) {
    var g := g1 as G;
    print g.Six, "\n";
  }

  method Test() {
    DoIt<E?>(null); // error: E? does not extend G
  }
}

module Example3 {
  trait G {
    const Three := 3
    const Six := Three + Three
  }

  class E extends G { }

  trait Thing<G1 extends G> {
    function GetG(): (g: G1)

    method PrintGSix() {
      var g1 := GetG();
      var g := g1 as G;
      print g.Six, "\n";
    }
  }

  class MyThing extends Thing<E?> { // error: E? does not extend G
    function GetG(): (g: E?) {
      null
    }
  }

  method Test() {
    var thing := new MyThing;
    thing.PrintGSix();
  }
}

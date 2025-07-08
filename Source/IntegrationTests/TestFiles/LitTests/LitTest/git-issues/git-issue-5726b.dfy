// RUN: %exits-with 4 %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Verification errors from Issue 5726 (see also git-issue-5726a.dfy)

module Example1 {
  trait G extends object {
    const Three := 3
    const Six := Three + Three
  }

  class E extends G { }

  method DoIt<G1 extends G?>(g1: G1) {
    var g := g1 as G; // error: g1 is a G?, but it might not be a G (because it might be null)
    print g.Six, "\n";
  }

  method CheckIt0<G1 extends G?>(g1: G1) {
    assert g1 is G?;
  }

  method CheckIt1<G1 extends G?>(g1: G1) {
    assert g1 is G; // error: g1 is a G?, but it might not be a G (because it might be null)
  }

  method Test() {
    DoIt<E?>(null);
  }
}

module Example2 {
  trait G extends object {
    const Three := 3
    const Six := Three + Three
  }

  class E extends G { }

  method DoIt<G1 extends G?>(g1: G1) {
    var g := g1 as G?;
    print g.Six, "\n"; // error: this is trying to deference a G?, but it is not known whether or not g is null
  }

  method Test() {
    DoIt<E?>(null);
  }
}

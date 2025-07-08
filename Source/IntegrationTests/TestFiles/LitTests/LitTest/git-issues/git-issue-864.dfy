// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M1 {
  trait {:termination false} T0 {
    const b: bool
  }
  trait T1 extends T0 {
  }
}

module M2 refines M1 {
  trait T1 {            // error: name T1 already used (since without the "...", this looks like a new trait)
    ghost predicate p() { b } // error: unresolved identifier: b
  }
}

module M3 refines M1 {
  trait T1 ... {
    ghost predicate p() { b }   // OK - the refined trait extends T0
  }
}

module M4 {
  import opened M1

  trait T1 {  // OK - a local declaration takes precedence over an imported one
  }
}


// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M1 {
  trait {:termination false} T0 {
    var b:bool
  }
  trait T1 extends T0 {
  }
}

module M2 refines M1 {
  trait T1 {            // error: name T1 already used
    predicate p() {b}
  }
}

module M3 refines M1 {
  trait T1 ... {
    predicate p() {b}   // OK - the refined trait extends T0
  }
}

module M4 {
  import opened M1

  trait T1 {  // OK - a local declaration takes precedence over an imported one
  }
}


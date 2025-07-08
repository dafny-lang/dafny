// RUN: %testDafnyForEachResolver "%s" -- --general-traits:datatype

module X {
  trait K { }
  trait {:termination false} A extends object, K {}
}

module Y {
  import opened X

  trait B extends A { }

  method Test(b: B) returns (a: A) {
    // The following assignment once caused malformed Boogie to be generated. The reason had been that
    // the resolver had not determined B to be a reference type. And that, in turn, had been caused by
    // that the opened import, effectively, had lost the "extends object" information.
    a := b;
  }
}

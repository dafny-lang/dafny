// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s" -- --general-traits:datatype

// The early-resolver code that figures out if a trait is a reference type or not is operating so early
// in the resolver pipeline that opened imports have not yet been resolved into the importing module.
// Thus, this early-resolver code looks directly into the top-level members of opened imports, but does
// so without consideration for possible ambiguities. This means that the early-resolver code may not
// properly figure out if a trait is a reference type or not. But if it gets it wrong, the ambiguity
// will still be reported as an error later in the resolver pipeline.
//
// This test file makes sure that the ambiguous-import errors are indeed being reported and that the
// resolver doesn't crash until then.

module X0 {
  // Here, A is a reference type
  trait {:termination false} A extends object {}
}

module X1 {
  // Here, A is not a reference type
  trait {:termination false} A {}
}

module X2 {
  // Here, A is not a reference type; in fact, it isn't even a type
  const A: object?
}

module Y01 {
  import opened X0
  import opened X1

  trait B extends A { // error: A is ambiguous
    function GetIndex(): nat
      reads this
  }
}

module Y10 {
  import opened X1
  import opened X0

  trait B extends A { // error: A is ambiguous
    function GetIndex(): nat
      reads this
  }
}

module Y0123 {
  import opened X0
  import opened X1
  import opened X2

  trait B extends A { // error: A is ambiguous
    function GetIndex(): nat
      reads this
  }
}

module Y210 {
  import opened X2
  import opened X1
  import opened X0

  trait B extends A { // error: A is ambiguous
    function GetIndex(): nat
      reads this
  }
}

module Z {
  import opened X0
  import opened X1
  import opened X2

}

module Z1 {
  import opened X0
  import opened X1
  import opened X2

  trait B extends X0.A { // no problem, since X0.A is fully qualified
    function GetIndex(): nat
      reads this // no problem, since B is a reference type
  }
}

module Z2 {
  import opened X0
  import opened X1
  import opened X2

  trait B extends X1.A { // no problem, since X1.A is fully qualified
    function GetIndex(): nat
      reads this // error: B is not a reference type
  }
}

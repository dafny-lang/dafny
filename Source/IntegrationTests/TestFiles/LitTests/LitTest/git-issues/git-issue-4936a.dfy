// RUN: %testDafnyForEachResolver "%s" -- --general-traits:datatype

module X {
  trait {:termination false} A extends object {}
}

module Y {
  import opened X

  trait B extends A {
    function GetIndex(): nat
      // The following once gave an error, complaining that B is not a reference type. The problem had been that
      // the opened import A was, effectively, hiding the information that A is a reference type.
      reads this
  }
}

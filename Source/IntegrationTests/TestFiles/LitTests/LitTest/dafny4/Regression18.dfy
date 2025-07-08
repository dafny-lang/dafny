// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


module A {
  type X
}

module B {
  import A

  type T = A.X
  type NewT = t: T | Pred(t) witness Witness()
  ghost predicate Pred(t: T)
  function Witness(): T
    ensures Pred(Witness())

  method Bad(x: T) returns (tt: NewT) {
    // The following once verified, because the LHS's type was normalized
    // past its constraints.
    tt := x;  // error: Pred(x) is unknown
  }

  method Good(x: T) returns (tt: NewT)
    requires Pred(x)
  {
    tt := x;  // fine
  }
}

module M {
  datatype Dt = SomeValue
  type X = Dt
  type T = t: X | true witness SomeValue

  ghost function G(t: X): int

  ghost function F(t: T): int {
    // this once used to give an error, because type checking/inference didn't skip
    // all intermediate layers of type synonyms when checking subtyping
    G(t)
  }
}

// RUN: %exits-with 4 %baredafny verify %args --region-checks:true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module SeparatedClasses {
  predicate {:invariant} WrongInvariant() { // Error: No invariant outside of classes
    true 
  }
  class Class {
    predicate {:invariant} InvariantWithArguments(a: int) { // Error: Invariants can't have arguments
      true
    }
    predicate {:invariant} InvariantWithTypeParameters<T>() { // Error: Invariants can't have type parameters
      true
    }
    predicate {:invariant} OneInvariant() { // OK
      true
    }
    predicate {:invariant} SecondInvariant() { // Error: Duplicate invariant
      true
    }
    function {:invariant} NotAnInvariant(): int { // Error: Functions can't be an invariant
      1
    }
  }
}
// RUN: %exits-with 4 %baredafny verify %args --region-checks:true "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module SeparatedClasses {
  predicate {:invariant} WrongInvariant() {
    true 
  }
  class Class {
    predicate {:invariant} OneInvariant() {
      true
    }
    predicate {:invariant} SecondInvariant() {
      true
    }
    function {:invariant} NotAnInvariant(): int {
      1
    }
  }
}
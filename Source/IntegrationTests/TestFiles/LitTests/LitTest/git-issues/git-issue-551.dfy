// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype VoidOutcome =
| VoidSuccess
| VoidFailure(error: string)
{
    predicate IsFailure() {
        this.VoidFailure?
    }
    function PropagateFailure(): VoidOutcome requires IsFailure() {
        this
    }
}

function Require(b: bool): (r: VoidOutcome) ensures r.VoidSuccess? ==> b
{
  if b then VoidSuccess else VoidFailure("failed")
}

ghost predicate MyPredicate() {
  true
}

method Main() returns (r: VoidOutcome) {
  // Verifies, but then fails to compile because MyPredicate isn't compiled
  r := Require(MyPredicate());
}


// RUN: %exits-with 4 %verify --type-system-refresh --check-invariants "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  predicate P() reads this
  invariant Foo() || P() // call to Foo should be illegal, because it does not open this
           // ^ error: decreases clause doesn't decrease
  predicate Foo()
    ensures P()
    reads this
  {
    assert this.invariant(); false
            // ^ error: cannot prove termination
  }
}
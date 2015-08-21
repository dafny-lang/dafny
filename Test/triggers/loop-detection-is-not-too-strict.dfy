// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test shows that the loop detection engine makes compromises when looking
// for subexpressions matching a trigger; in particular, it allows a
// subexpression to match a trigger without reporting a loop and without being
// equal to that trigger, as long as the only differences are variable

predicate P(x: int, y: int)

method Test() {
  // P(x, y) and P(y, x) might look like they would cause a loop. Since they
  // only differ by their variables, though, they won't raise flags.
  assume forall x: int, y: int :: P(x, y) == P(y, x);

  // This works independent of extra parentheses:
  assume forall x: int, y: int :: P(x, y) == (P(y, x));

  // Contrast with the following:
  assume forall x: int, y: int :: P(x, y) == P(x, y+1);
}

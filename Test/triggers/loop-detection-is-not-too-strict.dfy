// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This test shows that the loop detection engine makes compromises when looking
// for subexpressions matching a trigger; in particular, it allows a
// subexpression to match a trigger without reporting a loop and without being
// equal to that trigger, as long as the only differences are variable

ghost predicate P(x: int, y: int)
ghost predicate Q(x: int)

method Test(z: int) {
  // P(x, y) and P(y, x) might look like they would cause a loop. Since they
  // only differ by their variables, though, they won't raise flags.
  assume forall x: int, y: int :: P(x, y) == P(y, x);

  // This works independent of extra parentheses:
  assume forall x: int, y: int :: P(x, y) == (P(y, x));

  // Contrast with the following:
  assume forall x: int, y: int :: P(x, y) == P(x, y+1);

  // The following examples were made legal after an exchange where Chris
  // pointed examples in the IronClad sources where things like this were
  // incorrectly flagged.
  assert forall x :: true || Q(x) || Q(0);
  assert forall x :: true || Q(x) || Q(z);
  assert forall x :: true || P(x, 1) || P(x, z);

  // Support for the following was added following a discussion with Rustan; in
  // the second one the expression `if z > 1 then z else 3 * z + 1` is not
  // directly a constant expression, but it does not involve x, so it's ok:
  assert forall x :: true || Q(x) || Q(0+1);
  assert forall x :: true || Q(x) || Q(if z > 1 then z else 3 * z + 1);
  // Sanity check:
  assert forall x :: true || Q(x) || Q(if z > 1 then x else 3 * z + 1);

  // Let expressions are inlined before loop detection, causing this to get
  // correctly rewritten.
  assert forall x :: true || Q(x) || (var xx := x+1; Q(xx));
}

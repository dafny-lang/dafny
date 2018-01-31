// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file ensures that `old()` receives the special treatment that it
// requires; that is, `old(f(x))` is not less liberal than `f(x)`, and
// old(f(f(x))) does not loop with f(x) (doesn't it?)

class C { }
function f(c: C): C
function g(c: C): C
function h(c: C, i: int): C

method M(sc: set<C>)
  // Ensure that old(c) does not get picked as a trigger
  ensures forall c | c in sc :: true || c == old(f(c))

  // This checks whether loop detection handles `old` expressions properly.
  // In the first one f(c)/old(f(f(c))) is not reported as a loop. See
  // looping-is-hard-to-decide-modulo-equalities.dfy for an explanation.
  ensures forall c | c in sc :: true || f(c) == old(f(f(c)))
  ensures forall c | c in sc :: true || old(f(f(c))) == old(g(f(c))) || old(f(g(c))) == g(f(c)) || f(g(c)) == g(f(c))

  // These check that the final trigger filtering step doesn't get confused
  // between old expressions and regular expressions.
  ensures forall c | c in sc :: true || f(c) == old(g(f(c)))
  ensures forall c | c in sc :: true || f(c) == old(f(c)) || old(g(f(c))) == g(f(c))

  // WISH: A Dafny rewriter could cleanup expressions so that adding the
  //       expression forall c :: c == old(c) in a quantifier would cause a warning,
  //       instead of a trigger generation error as it does now.
{
}

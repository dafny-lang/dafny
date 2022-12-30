// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
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
  ensures forall c | c in sc :: true || c == old(f(c)) // warning: old has no effect

  // This checks whether loop detection handles `old` expressions properly.
  // In the first one f(c)/old(f(f(c))) is not reported as a loop. See
  // looping-is-hard-to-decide-modulo-equalities.dfy for an explanation.
  ensures forall c | c in sc :: true || f(c) == old(f(f(c))) // warning: old has no effect
  ensures forall c | c in sc :: true || old(f(f(c))) == old(g(f(c))) || old(f(g(c))) == g(f(c)) || f(g(c)) == g(f(c)) // warning (x3): old has no effect

  // These check that the final trigger filtering step doesn't get confused
  // between old expressions and regular expressions.
  ensures forall c | c in sc :: true || f(c) == old(g(f(c))) // warning: old has no effect
  ensures forall c | c in sc :: true || f(c) == old(f(c)) || old(g(f(c))) == g(f(c)) // warning (x2): old has no effect

  // WISH: A Dafny rewriter could cleanup expressions so that adding the
  //       expression forall c :: c == old(c) in a quantifier would cause a warning,
  //       instead of a trigger generation error as it does now.
{
}

function ff(c: C): C reads c

method MM(sc: set<C>)
  // Ensure that old(c) does not get picked as a trigger
  ensures forall c | c in sc :: true || c == old(ff(c))

  // This checks whether loop detection handles `old` expressions properly.
  // In the first one ff(c)/old(ff(ff(c))) is not reported as a loop. See
  // looping-is-hard-to-decide-modulo-equalities.dfy for an explanation.
  ensures forall c | c in sc :: true || ff(c) == old(ff(ff(c)))
  ensures forall c | c in sc :: true || old(ff(ff(c))) == old(g(ff(c))) || old(ff(g(c))) == g(ff(c)) || ff(g(c)) == g(ff(c))

  // These check that the final trigger filtering step doesn't get confused
  // between old expressions and regular expressions.
  ensures forall c | c in sc :: true || ff(c) == old(g(ff(c)))
  ensures forall c | c in sc :: true || ff(c) == old(ff(c)) || old(g(ff(c))) == g(ff(c))
{
}

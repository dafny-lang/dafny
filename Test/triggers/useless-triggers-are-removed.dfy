// RUN: %baredafny verify %args --print-tooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file ensures that Dafny does get rid of redundant triggers before
// annotating a quantifier, and that ths process does not interfere with cycle
// detection.

function f(x: int): int
function g(x: int): int
function h(x: int): int

method M()
  // In the following, only f(x) is kept. Note that the subset enumeration was
  // already smart enough to not build any trigger with multiple terms (it only
  // built 5 candidates)
  requires forall x: int :: f(x) + g(f(x)) + h(f(x)) + g(h(f(x))) + h(g(f(x))) == 0

  // Loop detection still works fine: in the following example, the trigger is
  // f(f(x))
  requires forall x: int :: f(x) == f(f(x))

  // This works for multi-triggers, too:
  requires forall x, y :: f(x) + g(f(y)) + g(y) + g(f(x)) == 0
{
}

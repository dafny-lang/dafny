// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type t = seq<int>

predicate P(x:t)
function F(x:t) : int
function C() : int { assume (exists x :: P(x)); var x :| P(x); F(x) }

lemma L(x:t)
{
  assume P(x);
  assume forall y :: P(y) ==> y == x;
  assert F(x) == C(); // FAILS
}

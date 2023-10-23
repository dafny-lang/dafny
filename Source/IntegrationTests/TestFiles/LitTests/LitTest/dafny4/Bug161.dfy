// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type t = seq<int>

ghost predicate P(x:t)
ghost function F(x:t) : int
ghost function C() : int { assume (exists x :: P(x)); var x :| P(x); F(x) }

lemma L(x:t)
{
  assume P(x);
  assume forall y :: P(y) ==> y == x;
  assert F(x) == C(); // FAILS
}
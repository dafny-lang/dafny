// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate R(x: int)

inductive lemma P(x: int)
{
  forall x | R(x)
  {
  }
}
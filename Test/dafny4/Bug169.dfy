// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate R(x: int)

least lemma P(x: int)
{
  forall x | R(x)
  {
  }
}

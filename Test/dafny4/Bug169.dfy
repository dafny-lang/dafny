// RUN: %dafny /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate R(x: int)

least lemma P(x: int)
{
  forall x | R(x)
  {
  }
}

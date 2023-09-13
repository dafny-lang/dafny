// RUN: %testDafnyForEachResolver "%s"


ghost predicate R(x: int)

least lemma P(x: int)
{
  forall x | R(x)
  {
  }
}

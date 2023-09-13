// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


lemma P0(x: int)
  requires X: x == 17
{
  assert x == 17;  // error: because X hasn't been revealed
}

lemma P1(x: int)
  requires X: x == 17
{
  reveal X;
  assert x == 17;  // this verifies, because X has been revealed
}

least lemma Q(x: int)
  requires X: x == 17
{
  assert x == 17;  // error: because X has not been revealed
}

greatest lemma R(x: int)
  requires X: x == 17
{
  assert x == 17;  // error: because X hasn't been revealed
}

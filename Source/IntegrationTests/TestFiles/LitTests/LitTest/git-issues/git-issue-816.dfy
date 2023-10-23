// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

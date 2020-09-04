// RUN: %dafny /compile:0 "%s" > "%t"
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

inductive lemma Q(x: int)
  requires X: x == 17
{
  assert x == 17;  // this SHOULD be an error, but it isn't; evidently, the X is ignored
}

colemma R(x: int)
  requires X: x == 17
{
  assert x == 17;  // error: because X hasn't been revealed
}


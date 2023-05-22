// RUN: %exits-with 4 %dafny   "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma T(a: int) returns (b: int)
  ensures a == b
{
  calc {
    a;
  }
}

lemma A(i: int)
  ensures false
{
  if * {
  } else {
  }
}
// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost const maxi := 4;

type substring = x: string | |x| < maxi

// It's ok to have not compiled subset types in all specification expressions
method test(s: seq<substring>) returns (r: int)
  requires forall x: substring :: x in s ==> |x| < maxi
  ensures forall x: substring :: x in s ==> |x| < maxi
{
  for j := 0 to 5
    invariant forall x: substring :: x in s ==> |x| < maxi + 5 - j
  {
    r := j;
  }
  assert forall x: substring :: x in s ==> |x| < maxi;
  while true
    invariant forall x: substring :: x in s ==> |x| < maxi
  {
    break;
  }
  calc {
    forall x: substring :: x in s ==> |x| < maxi;
    forall x: substring :: x in s ==> |x| < maxi;
  }
}

ghost function testf(s: seq<substring>): (r: int)
  requires forall x: substring :: x in s ==> |x| < maxi
  ensures forall x: substring :: x in s ==> |x| < maxi
{
  0
}
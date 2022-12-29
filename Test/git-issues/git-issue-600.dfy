// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype D = D(n: int)

function f(s: seq<int>): int
  requires |s| != 0
  ensures f(s) in s
{
  s[0]
}

predicate vacuous_fact(ds: seq<D>, s: seq<int>)
{
  0 in s && |s| == 0 ==> ds[f(s)].n == 0
}

lemma False()
  ensures false  // error: this postcondition does not hold
{
  assert vacuous_fact([], []);
}

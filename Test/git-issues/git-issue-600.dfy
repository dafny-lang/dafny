// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


datatype D = D(n: int)

ghost function f(s: seq<int>): int
  requires |s| != 0
  ensures f(s) in s
{
  s[0]
}

ghost predicate vacuous_fact(ds: seq<D>, s: seq<int>)
{
  0 in s && |s| == 0 ==> ds[f(s)].n == 0
}

lemma False()
  ensures false  // error: this postcondition does not hold
{
  assert vacuous_fact([], []);
}

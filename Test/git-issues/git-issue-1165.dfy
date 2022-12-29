// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method P()

method TestMapMethod(s0: set<int>, s1: set<int>) {
  var m;
  m := map key | key in (s0 + s1) && P() :: true;
  m := map key | key in (s0 + s1) :: true;
  m := map key | key in s0 + s1 && P() :: true;
  m := map key | key in s0 + s1 :: true;
  assert true;
}

function TestMap(s0: set<int>, s1: set<int>): bool {
  // Once, these caused malformed Boogie, because the parentheses had fooled the
  // RewriteInExpr mechanism when generating CanCall assumptions.
  // Ditto for the comprehensions in functions below.
  var m0 := map key | key in (s0 + s1) && P() :: true;
  var m1 := map key | key in (s0 + s1) :: true;
  var m2 := map key | key in s0 + s1 && P() :: true;
  var m3 := map key | key in s0 + s1 :: true;
  true
}

function TestSet(s0: set<int>, s1: set<int>): bool {
  var t0 := set key | key in (s0 + s1) && P() :: key;
  var t1 := set key | key in (s0 + s1) :: key;
  var t2 := set key | key in s0 + s1 && P() :: key;
  var t3 := set key | key in s0 + s1 :: key;
  true
}

function TestInMultiset(s0: multiset<int>, s1: multiset<int>): bool {
  var t0 := set key | key in (s0 + s1) && P() :: key;
  var t1 := set key | key in (s0 + s1) :: key;
  var t2 := set key | key in s0 + s1 && P() :: key;
  var t3 := set key | key in s0 + s1 :: key;
  true
}

class Cell { var data: int }

method ModifiesClauses(S: set<object>, T: set<object>, p: Cell, q: Cell, n: int)
  requires p in S + T
  requires q in S
  modifies S + T
{
  p.data := n;
  q.data := n;
}

function Id(S: set<object>): set<object> { S }

method Fresh0(p: Cell, q: Cell, n: int) returns (S: set<object>, T: set<object>)
  ensures fresh(S - T)
{
  S, T := {p}, {p};
}

method Fresh1(p: Cell, q: Cell, n: int) returns (S: set<object>, T: set<object>)
  ensures fresh(Id(S) - Id(T))
{
  S, T := {p}, {p};
}

method Fresh2(p: Cell, q: Cell, n: int) returns (S: set<object>, T: set<object>)
  ensures fresh(Id(S - T))
{
  S, T := {p}, {p};
}

function ReadsClauses(S: set<object>, T: set<object>, p: Cell, q: Cell, n: int): int
  requires p in S + T
  requires q in S
  reads S + T
{
  p.data + q.data + n
}

twostate predicate FreshInFunction(S: set<object>, T: set<object>)
{
  fresh(S + T)
}

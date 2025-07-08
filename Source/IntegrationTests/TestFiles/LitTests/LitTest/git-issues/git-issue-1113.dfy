// RUN: %testDafnyForEachResolver "%s"


// ---------- 1113 ----------

type pair = s:seq<int> | |s| == 2 witness [0,0]

ghost function id<T>(x: T): T { x }

ghost function fst(p: pair): int
{
  id(p)[0] // this once gave a type-checking error
}

ghost function pair_id(p: pair): seq<int>
{
  id(p)[0..2] // this once gave a type-checking error
}

ghost function pair_to_seq(p: pair): seq<int> { p }

method stuff_that_works(p: pair)
{
  var _: int := p[0];
  var _: seq<int> := p[0..1];
  var _: seq<int> := id(p);
  var _: int := pair_to_seq(p)[1];
  var _: seq<int> := pair_to_seq(p)[0..1];
}

// ---------- 1157 ----------

type subString = x: seq<char> | 0 <= |x| < 0x8000_0000

function foo(s: subString): subString { "0" }

method goo(s: subString) returns (eq: bool)
{
  if s != [] {
    ghost var s' := foo(s[0..]);
    assert s'[1..] == []; // this once gave a type-checking error
  }
  return true;
}

// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ---------- 1113 ----------

type pair = s:seq<int> | |s| == 2 witness [0,0]

function id<T>(x: T): T { x }

function fst(p: pair): int
{
  id(p)[0] // this once gave a type-checking error
}

function pair_id(p: pair): seq<int>
{
  id(p)[0..2] // this once gave a type-checking error
}

function pair_to_seq(p: pair): seq<int> { p }

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

function method foo(s: subString): subString { "0" }

method goo(s: subString) returns (eq: bool)
{
  if s != [] {
    ghost var s' := foo(s[0..]);
    assert s'[1..] == []; // this once gave a type-checking error
  }
  return true;
}

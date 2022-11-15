// RUN: %baredafny verify %args_0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type foo = m: map<int, int> | forall n <- m.Keys :: m[n] < 5

function addToFoo(m: foo): foo
  ensures false
{
  m[1 := 7]
}

type seq0 = s: seq<int> | forall n <- s :: n == 0

function ReplaceInSeq0(s: seq0): seq0
  requires |s| > 0
  ensures false
{
  s[0 := 1]
}

type map0 = m: map<int, int> | forall k <- m :: m[k] == 0

function ReplaceInMap0(m: map0): map0
  requires 0 in m
  ensures false
{
  m[0 := 1]
}

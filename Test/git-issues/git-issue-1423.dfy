// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(s: seq)

method M(s: seq<int>, i: nat, v: int, n: nat)
  requires i < n <= |s|
  requires P(s[n..])
{
  var t := s[i := v];
  // Before issue 1423 was fixed, the following assertion did not prove automatically
  assert P(t[n..]);
}

method Workaround(s: seq<int>, i: nat, v: int, n: nat)
  requires i < n <= |s|
  requires P(s[n..])
{
  var t := s[i := v];
  assert s[n..] == t[n..];
  assert P(t[n..]);
}

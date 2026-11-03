// RUN: %baredafny generate-tests Spec --bva 100 --fdnf "%s" > "%t"
// RUN: grep -v "^include" "%t" > "%t.tmp"
// RUN: %diff "%s.expect" "%t.tmp"

method ConditionalGet(s: seq<int>, x: int) returns (r: int)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures x < 0 ==> r == -1
  ensures x >= |s| ==> r == -2
  ensures 0 <= x < |s| ==> r == s[x]
{ }
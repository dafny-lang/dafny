// RUN: %baredafny generate-tests Spec --simplify "%s" > "%t"
// RUN: grep -v "^include" "%t" > "%t.tmp"
// RUN: %diff "%s.expect" "%t.tmp"

method {:testEntry} Classify(x: int) returns (r: int)
  ensures x > 0 ==> r == 1
  ensures x == 0 ==> r == 0
  ensures x < 0 ==> r == -1
{ }
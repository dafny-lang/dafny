// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file is a series of basic tests for loop detection, focusing on the
// warnings and information messages

ghost function f(i: int): int
ghost function g(i: int): int

method M() {
  assert forall i :: false ==> f(i) == f(f(i));
  assert forall i :: false ==> f(i) == f(i+1);
  assert forall i {:matchingloop} :: false ==> f(i) == f(i+1);

  assert forall i :: false ==> f(i) == f(i+1) && f(i) == g(i);
  assert forall i :: false ==> f(i) == f(i+1) && f(i) == f(i);
  assert forall i {:matchingloop} :: false ==> f(i) == f(i+1) && f(i) == f(i);

  assert forall i :: false ==> f(i) == 0;
  assert forall i :: false ==> f(i+1) == 0;
  assert forall i {:autotriggers false} :: false ==> f(i+1) == 0;

  assert forall i, j: int :: false ==> f(i) == f(j);
  assert forall i, j: int :: false ==> f(i) == f(i);
  assert forall i, j: int :: false ==> f(i) == f(i) && g(j) == 0;
  assert forall i, j: int :: false ==> f(i) == f(i) && g(j+1) == 0;
  assert forall i, j: int {:autotriggers false} :: false ==> f(i) == f(i);
  assert forall i, j: int {:trigger f(i), g(j)} :: false ==> f(i) == f(i);
}

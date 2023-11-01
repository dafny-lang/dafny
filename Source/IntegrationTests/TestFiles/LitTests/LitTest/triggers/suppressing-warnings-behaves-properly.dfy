// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file checks that suppressing warnings works properly

ghost predicate f(x: int)
ghost predicate g(x: int)

method M() {
  assert forall n :: n >= 0 || n < 0;
  assert forall n {:nowarn} :: n >= 0 || n < 0;
  assert forall n {:autotriggers false} :: n >= 0 || n < 0;

  assert forall n: nat :: (n != 0) == f(n) || true;
  assert forall n: nat {:nowarn} :: (n != 0) == f(n) || true;
  assert forall n: nat {:autotriggers false} :: (n != 0) == f(n) || true;

  assert forall n: nat :: f(n) == f(n+1) || g(n) || true;
  assert forall n: nat {:nowarn} :: (n != 0) == f(n) || true;
  assert forall n: nat {:autotriggers false} :: (n != 0) == f(n) || true;
}

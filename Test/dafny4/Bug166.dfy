// RUN: %baredafny verify %args --disable-nonlinear-arithmatic "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate P(x:int)

method test(s:seq<int>)
    ensures forall x :: x > 5 ==> P(x);
    ensures forall i :: 0 <= i < |s| ==> P(s[i]);

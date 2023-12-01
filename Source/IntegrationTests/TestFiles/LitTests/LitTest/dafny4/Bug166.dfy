// RUN: %verify --disable-nonlinear-arithmetic "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate P(x:int)

method test(s:seq<int>)
    ensures forall x :: x > 5 ==> P(x)
    ensures forall i :: 0 <= i < |s| ==> P(s[i])

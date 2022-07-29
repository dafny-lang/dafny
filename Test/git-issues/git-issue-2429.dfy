// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait Spec<Q(==, 00)> {
  method M(t: Q)
    ensures var t: Q :| true; |multiset{}[t := 1]| == 1
    ensures |map[t := t][t := t]| == 1
    ensures |[t][0 := t]| == 1
}

class Impl extends Spec<object?> {
  method M(t: object?)
    ensures var t: object? :| true; |multiset{}[t := 1]| == 1
    ensures |map[t := t][t := t]| == 1
    ensures |[t][0 := t]| == 1
}

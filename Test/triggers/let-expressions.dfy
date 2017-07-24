// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:1 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate Foo(s: seq<int>)
{
    forall i :: 0 <= i < |s| ==> var j := i; s[j] > 0
}

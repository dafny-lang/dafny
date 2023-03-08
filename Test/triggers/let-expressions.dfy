// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost predicate Foo(s: seq<int>)
{
    && (forall i :: 0 <= i < |s| ==> var j := i; s[j] > 0)
    && (forall i :: 0 <= i < |s| ==> var j, k := i, i; s[k] > 0)
    && (forall i :: 0 <= i < |s|-1 ==> s[i] == s[i+1])
    && (forall i :: 0 <= i < |s|-1 ==> s[i] == var j := i+1; s[j])
}

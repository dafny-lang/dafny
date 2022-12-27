// RUN: %exits-with 2 %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate Foo(s: seq<int>)
{
    // Does not work
    && (forall i :: 0 <= i < |s| ==>
      && i is nat)
}

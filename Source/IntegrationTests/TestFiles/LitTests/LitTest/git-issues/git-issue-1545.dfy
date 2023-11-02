// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


ghost predicate Foo(s: seq<int>)
{
    // Does not work
    && (forall i :: 0 <= i < |s| ==>
      && i is nat)
}

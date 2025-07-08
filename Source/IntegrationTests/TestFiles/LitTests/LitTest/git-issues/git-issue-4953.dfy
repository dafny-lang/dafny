// RUN: %testDafnyForEachResolver "%s" --expect-exit-code=2

// The lookup of a non-existing member once caused a crash in the new resolver.

function Foo(): (result: seq<int>)
  ensures result.NonExistingMember

function Bar(formal: seq<int>): int
  requires formal.NonExistingMember

method Zap(i: seq<int>) returns (o: seq<int>) {
  var local: seq<int> := [];

  var a := i.NonExistingMember;
  var b := o.NonExistingMember;
  var c := local.NonExistingMember;
}

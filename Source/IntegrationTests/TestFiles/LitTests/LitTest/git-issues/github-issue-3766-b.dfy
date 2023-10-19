// RUN: %baredafny run --target:java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// bad.dfy for 3766
datatype Tree = Tree(ts: seq<Tree>)

datatype Nothing<T> = Nothing
{
  predicate IsFailure() { false }
}

method Main() {
  var nothing: Nothing<Tree> := Nothing;
  :- expect nothing;
}
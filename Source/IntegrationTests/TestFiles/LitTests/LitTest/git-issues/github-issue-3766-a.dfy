// RUN: %baredafny run --target:java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// good.dfy for 3766
datatype Tree = Tree(ts: seq<Tree>)

datatype Nothing = Nothing
{
  predicate IsFailure() { false }
}

method Main() {
  var nothing: Nothing := Nothing;
  :- expect nothing;
}
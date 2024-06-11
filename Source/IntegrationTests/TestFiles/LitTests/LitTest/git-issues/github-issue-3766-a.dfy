// RUN: %testDafnyForEachCompiler "%s"

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
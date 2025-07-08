// RUN: %testDafnyForEachCompiler "%s"

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
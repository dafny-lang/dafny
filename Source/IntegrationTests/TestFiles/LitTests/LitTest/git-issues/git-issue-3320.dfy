// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

datatype Dt = A | B(b: set<nat>)

function SetComprehension(s: seq<Dt>): set<nat> {
  set i, b | 0 <= i < |s| && s[i].B? && b in s[i].b && 1 != 2 :: b
}

function MapComprehension(s: seq<Dt>): map<int, int> {
  map i, b | 0 <= i < |s| && s[i].B? && b in s[i].b && 1 != 2 :: b := b
}

method Main() {
  var s := [A, B({0})];
  print SetComprehension(s), "\n";
  print MapComprehension(s), "\n";
}
// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

datatype Dt = A | B(b: set<nat>)

function SetComprehension(sr: seq<Dt>): set<nat> {
  set i, b | 0 <= i < |sr| && sr[i].B? && b in sr[i].b && 1 != 2 :: b
}

function MapComprehension(sr: seq<Dt>): map<int, int> {
  map i, b | 0 <= i < |sr| && sr[i].B? && b in sr[i].b && 1 != 2 :: b := b
}

method Main() {
  var sr := [A, B({0})];
  print SetComprehension(sr), "\n";
  print MapComprehension(sr), "\n";
}
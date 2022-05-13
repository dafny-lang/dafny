// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost const zero := 0
type GhostNat = x : int | x >= zero
const S: set<int> := {-1, 0, 1};
type GhostNatInS = x : int | x in (set j: GhostNat | j in S)

function method FailIfNotGhostNatInS(i: GhostNatInS): int {
  if i < 0 then 1/0 else i
}

method Main() {
  var s := forall x: GhostNatInS | x in S :: FailIfNotGhostNatInS(x) == x;
  print s;
}
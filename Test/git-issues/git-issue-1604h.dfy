// RUN: %dafny /compile:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost const zero := 0
type GhostNat = x : int | x >= zero
const S: set<int> := {-1, 0, 1};
type GhostNatInS = x : int | x in (set j: GhostNat | j in S)

function method FailIfNotGhostNat(i: GhostNat): int {
  if i < 0 then 1/0 else i
}

method Main() {
  var s := forall x: GhostNatInS | x in S :: FailIfNotGhostNat(x) == x;
  print s;
}
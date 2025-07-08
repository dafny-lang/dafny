// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

function returnNat(c: nat): int
{
  if c < 0 then 1/0 else c
}

method Main() {
  var x: set<int> := { -1, 2, -3, 4 };
  var y := set c: nat | c in x;
  var b := forall c :: c in y ==> returnNat(c) >= 0;
  assert b;
  print b;
}


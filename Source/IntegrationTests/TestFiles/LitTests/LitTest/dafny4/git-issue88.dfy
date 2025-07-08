// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

type Grid = array2<int>

method M2() {
  var g: Grid := new int[9,9];
  g[0,0] := 1;
}

type Line = array<int>

method M1() {
  var g: Line := new int[9];
  g[0] := 1;
}

method Main()
{
  M2();
  M1();
}

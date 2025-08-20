// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

method Test(len: int, a: seq<int>) {
  var len := |a|;
}
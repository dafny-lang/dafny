// RUN: %testDafnyForEachCompiler %s

class X {
  var x: int
  invariant x >= 0
}
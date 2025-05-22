// RUN: %testDafnyForEachCompiler %s

class X {
  method MutateX()
    requires x >= 0
    modifies this
  { x := 0; }
  var x: int
  invariant x >= 0
}
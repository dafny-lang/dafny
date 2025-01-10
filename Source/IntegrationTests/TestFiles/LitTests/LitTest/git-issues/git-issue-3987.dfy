// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

datatype D = A

method Main() {
  //Clone
  match A {
    case A =>
      var a: array<nat> := new nat[1](i => i);
      forall i | 0 <= i < a.Length {
        a[i] := i;
      }
  }
  print "pass\n";
}

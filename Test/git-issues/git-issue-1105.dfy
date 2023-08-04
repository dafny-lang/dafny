// RUN: %testDafnyForEachCompiler "%s"

// Regression: A constructor like PushOp with 1+ ghost parameters and 0 non-ghost parameters
// once caused the Java compiler to emit two 0-parameter constructors

datatype Op =
  | NoOp
  | PushOp(ghost id: int)

method Main() {
  var o := PushOp(20);
  print o, "\n";
}

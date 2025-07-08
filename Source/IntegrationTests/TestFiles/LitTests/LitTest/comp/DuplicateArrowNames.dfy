// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

// Previously, this would lead to duplicate variable names in Java, C#,
// and Python.
method Main() {
  var f: nat -> nat -> bool;
  print f(0)(1), "\n";
}

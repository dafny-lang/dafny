// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

module A.base {
  datatype Dt = Dt
}

method Main() {
  print A.base.Dt, "\n";
}

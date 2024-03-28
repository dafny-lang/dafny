// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

module A.try {
  datatype Dt = Dt
}

method Main() {
  print A.try.Dt, "\n";
}

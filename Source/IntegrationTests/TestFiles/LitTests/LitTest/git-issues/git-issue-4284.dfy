// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --compile-suffix --enforce-determinism

method Main() {
  print (true, false), "\n";
}

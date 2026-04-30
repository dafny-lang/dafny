// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --enforce-determinism

method Main() {
  print "Mikaël fixed UTF8\n";
}

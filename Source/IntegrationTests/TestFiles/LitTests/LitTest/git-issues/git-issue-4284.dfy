// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --compile-suffix

method Main() {
  print (true, false), "\n";
}

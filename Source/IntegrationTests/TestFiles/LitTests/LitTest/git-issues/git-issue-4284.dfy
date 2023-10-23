// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --compile-suffix

method Main() {
  print (true, false), "\n";
}

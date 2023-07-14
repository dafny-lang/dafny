// RUN: %testDafnyForEachCompiler "%s" -- --compile-suffix

method Main() {
  print (true, false), "\n";
}

// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

method Main() {
  print "XYZ"; // Checks that no extra newline is added to the output
}

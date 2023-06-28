// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment --unicode-char:false

method Main() {
  print "XYZ"; // Checks that no extra newline is added to the output
}

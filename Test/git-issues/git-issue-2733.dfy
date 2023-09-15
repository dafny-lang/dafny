// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment --unicode-char:false

method Main() {
  print "XYZ"; // Checks that no extra newline is added to the output
}

// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0

// This file tests that it's okay for a filename to start with a digit.

method Main() {
  print "hello\n";
}

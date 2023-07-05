// RUN: %testDafnyForEachCompiler "%s"

// This file tests that it's okay for a filename to start with a digit.

method Main() {
  print "hello\n";
}

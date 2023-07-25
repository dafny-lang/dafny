// RUN: %testDafnyForEachCompiler "%s"

// This file tests that it's okay for a filename to have a name like "class, which is
// reserved in many languages.

method Main() {
  print "hello\n";
}

// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello, World! Best, Dafny\n";
}

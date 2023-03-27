// RUN: %baredafny test "%s" > "%t"
// RUN: %baredafny run "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Main\n";
}

method {:test} Test() {
  print "Test\n";
}

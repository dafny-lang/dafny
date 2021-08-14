// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %dafny /compile:3 /trackPrintEffects:1 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "hello, Main\n"; // error: cannot print from this method
  P(); // error: cannot call printing method
}

method {:print} P() {
  print "method P here\n";
  M();
}

method M() {
  var x := F(3);
  print "bye, from M\n"; // error: cannot print from this method
}

function F(x: int): int {
  10
} by method {
  print "function-by-method F\n"; // error: cannot print from this method
  return 10;
}

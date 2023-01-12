// RUN: %baredafny build -t:java "%s" org/D.java > "%t"
// RUN: java -cp B.jar org.D >> "%t"
// RUN: %diff "%s.expect" "%t"
// XFAIL: *

// Fails on integration tests because the file org/D.java is not put in the right place.
method m() {
  print "Hello, World!\n";
}

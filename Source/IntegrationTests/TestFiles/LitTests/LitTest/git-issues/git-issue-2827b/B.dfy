// RUN: %baredafny build -t:java "%s" "%S"/org/D.java > "%t"
// RUN: java -cp "%S"/B.jar org.D >> "%t"
// RUN: %diff "%s.expect" "%t"

// Fails on integration tests because the file org/D.java is not put in the right place.
method m() {
  print "Hello, World!\n";
}

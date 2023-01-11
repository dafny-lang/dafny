// RUN: %baredafny build -t:java "%s" org/D.java > "%t"
// RUN: java -cp B.jar org.D >> "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  print "Hello, World!\n";
}

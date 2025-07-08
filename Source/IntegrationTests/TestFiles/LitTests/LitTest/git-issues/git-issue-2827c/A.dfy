// RUN: %baredafny build -t:java --output "%S/Q.jar" "%s" > "%t"
// RUN: java -jar "%S/Q.jar" >>  "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello, World!\n";
}

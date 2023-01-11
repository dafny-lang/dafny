// RUN: %baredafny build -t:java "%s" > "%t"
// RUN: java -jar A.jar >>  "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello, World!\n";
}

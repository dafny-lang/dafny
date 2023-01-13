// RUN: %baredafny build -t:java --output zzz/Q.jar "%s" > "%t"
// RUN: java -jar zzz/Q.jar >>  "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello, World!\n";
}

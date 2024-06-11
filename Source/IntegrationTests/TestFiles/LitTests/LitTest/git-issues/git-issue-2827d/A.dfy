// RUN: %baredafny build -t:java --output "%S/zzz/Q.jar" "%s" > "%t"
// RUN: java -jar "%S/zzz/Q.jar" >>  "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello, World!\n";
}

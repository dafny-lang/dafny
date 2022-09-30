// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Mikaël fixed UTF8\n";
}

// RUN: %baredafny run --quiet:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Done\n";
}

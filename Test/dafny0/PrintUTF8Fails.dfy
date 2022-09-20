// RUN: %dafny_0 /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Mikaël did not fix 😎\n";
}

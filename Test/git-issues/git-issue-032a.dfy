// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method m() {
  var x := ();
  match x { case () => print "OK"; case _ => print "DEF"; }
  print "\n";
}


// RUN: %testDafnyForEachResolver "%s" -- --allow-warnings


method m() {
  var x := ();
  match x { case () => print "OK"; case _ => print "DEF"; }
  print "\n";
}


// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"


method Main() {
  m();
  mm();
}

method m() {
  var x := (2,3);
  match x { case (2,y) => print "OK",y; case _ => print "DEF"; }
  print "\n";
  match x { case zz => print "OK"; case _ => print "DEF"; } // warning
  print "\n";
}

method mm() {
  var x := ();
  match x { case () => print "OK"; }
  match () { case () => print "OK"; }
  print "\n";
  var z := match x { case () => 0 case _ => 1 }; // warning
  var y := match () { case () => 0 case _ => 1 }; // warning
  print z, y, "\n";
}




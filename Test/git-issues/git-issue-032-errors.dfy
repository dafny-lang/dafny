// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method errors() {
  var e := ();
  var x := (2,3);
  match x { case () => print "OK"; case _ => print "BAD"; }
  match e { case (a,b) => print "OK"; case _ => print "BAD"; }
  match () { case (a,b) => print "OK"; case _ => print "BAD"; }
  var z := match x { case () => 0 case _ => 1};
  var y := match e { case (a,b) => 0 case _ => 1};
  var w := match () { case (a,b) => 0 case _ => 1};
}




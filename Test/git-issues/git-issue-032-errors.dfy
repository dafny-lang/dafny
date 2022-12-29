// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


method errors() {
  var e := ();
  var x := (2,3);
  match x { case () => print "OK"; case _ => print "BAD"; }  // ERROR
  match e { case (a,b) => print "OK"; case _ => print "BAD"; } // ERROR
  match () { case (a,b) => print "OK"; case _ => print "BAD"; } // ERROR
  var z := match x { case () => 0 case _ => 1}; // ERROR
  var y := match e { case (a,b) => 0 case _ => 1}; // ERROR
  var w := match () { case (a,b) => 0 case _ => 1}; // ERROR
}




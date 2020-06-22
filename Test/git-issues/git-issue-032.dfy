// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function t2(a: int, b:int): (int,int) { (a,b) }
function t0(): () { () } 

method Main() {
  m();
  mm();
  mmm();
}
   
method m() {
  var x := (2,3);
  match x { case (2,y) => print "OK",y; case _ => print "DEF"; }
  print "\n";
}
   
method mm() {
  var x := (2,3);
  match x { case () => print "OK"; case _ => print "DEF"; }
  print "\n";
}
   
method mmm() {
  var x := ();
  match x { case () => print "OK"; }
  print "\n";
}
   



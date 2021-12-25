// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// To enable this in cs we need to implement DowncastClone for datatypes.
// Java avoids this problem by not even allowing traits in datatypes.

datatype Co<+T> = Co(T)
datatype Con<-T> = Con(T -> bool)

trait X {}

class Y extends X {
  constructor Y() {}
}

method DowncastCo() {
  var i := new Y.Y();
  var a: Co<X> := Co(i);
  var b: Co<Y>;
  b := a;
  print a, " and ", b, "\n";
}

method DowncastCon() {
  var i: Con<X> := Con(_ => false);
  var a: Con<Y> := i;
  var b: Con<X>;
  b := a;
  print a, " and ", b, "\n";
}

method Main(){
  DowncastCo();
  DowncastCon();
  print "Done\n";
}

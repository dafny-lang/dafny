// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// To enable this in cs we need to implement DowncastClone for datatypes.
// Java avoids this problem by not even allowing traits in datatypes.

datatype Co<+T> = Co(T)
datatype Contra<-T> = Contra(f: T -> bool)

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

method DowncastContra() {
  var y := new Y.Y();
  var i: Contra<X> := Contra(_ => false);
  var a: Contra<Y> := i;
  var b: Contra<X>;
  b := a;
  print a.f(y), " and ", b.f(y), "\n";
}

method DowncastFunc() {
  var i := new Y.Y();
  var a: bool -> X := (_ => i);
  var b: bool -> Y;
  b := a;
  print a(false), " and ", b(false), "\n";
}

method Main(){
  DowncastCo();
  DowncastContra();
  DowncastFunc();
  print "Done\n";
}

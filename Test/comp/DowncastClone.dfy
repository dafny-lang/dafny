// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny_0 /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// To enable this in cs we need to implement DowncastClone for datatypes.
// Java avoids this problem by not even allowing traits in datatypes.

datatype Co<+T> = Co(T) | C
datatype ReCo<+T> = ReCo(T)
datatype Contra<-T> = Contra(f: T -> bool) | C
datatype ReContra<-T> = ReContra(f: T -> bool)

trait X {}

class Y extends X {
  constructor () {}
}

method DowncastCo() {
  var i := new Y();
  var a: Co<X> := Co(i);
  var b: Co<Y>;
  b := a;
  print a, " and ", b, "\n";
}

method DowncastReCo() {
  var i := new Y();
  var a: ReCo<X> := ReCo(i);
  var b: ReCo<Y>;
  b := a;
  print a, " and ", b, "\n";
}

method DowncastContra() {
  var y := new Y();
  var i: Contra<X> := Contra(_ => false);
  var a: Contra<Y> := i;
  var b: Contra<X>;
  b := a;
  print a.f(y), " and ", b.f(y), "\n";
}

method DowncastReContra() {
  var y := new Y();
  var i: ReContra<X> := ReContra(_ => false);
  var a: ReContra<Y> := i;
  var b: ReContra<X>;
  b := a;
  print a.f(y), " and ", b.f(y), "\n";
}

method DowncastFunc() {
  var i := new Y();
  var a: bool -> X := (_ => i);
  var b: bool -> Y;
  b := a;
  print a(false), " and ", b(false), "\n";
}

method Main(){
  DowncastCo();
  DowncastReCo();
  DowncastContra();
  DowncastFunc();
  print "Done\n";
}

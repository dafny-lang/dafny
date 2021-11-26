// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"
// To enable this in cs we need to implement DowncastClone for datatypes.
// Java avoids this problem by not even allowing traits in datatypes.

datatype Co<+T> = Co(T)

trait X {}

class Y extends X {
  constructor Y() {}
}

method Downcast() {
  var i := new Y.Y();
  var a: Co<X> := Co(i);
  var b: Co<Y>;
  b := a;
  print a, " and ", b, "\n";
}

method Main(){
  Downcast();
  print "Done\n";
}

// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Record = Record(a: int, ghost b: int)

function method TwinPrimes(): Record {
  Record(41, 43)
}

method Main() {
  var u := var Record(x, y) := TwinPrimes(); y; // x is non-ghost
  var w := var Record(x, y) := TwinPrimes(); x; // x and w are non-ghost
  //@ assert u == 43;
  print w, "\n";
}

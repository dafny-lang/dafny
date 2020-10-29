// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

function TwinPrimes(): (int, int) {
  (41, 43)
}

function method TwinPrimesM(): (int, int) {
  (41, 43)
}

method Main() {
  var (x, y) := TwinPrimesM();  // x and y are not ghost
  var p := TwinPrimesM();  // p is not ghost
  print x, " ", y, " ", p, "\n"; // OK
}


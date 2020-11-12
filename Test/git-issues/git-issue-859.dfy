// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype FailureCompatible = Make {
  predicate method IsFailure() { true }
  function method PropagateFailure(): int { 12 }
  method Extract() returns (r: real) { }
}

method M() returns (r: FailureCompatible) { }

method N() returns (x: int) {
  var s: real :- M();
  return 13;
}

method Main() {
  var x := N();
  print x, "\n";
}


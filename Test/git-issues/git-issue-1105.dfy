// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Regression: A constructor like PushOp with 1+ ghost parameters and 0 non-ghost parameters
// once caused the Java compiler to emit two 0-parameter constructors

datatype Op =
  | NoOp
  | PushOp(ghost id: int)

method Main() {
  var o := PushOp(20);
  print o, "\n";
}

// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %exits-with 3 %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Level1 = Level1(u:int)
datatype Level2 = Level2(u:int, l:Level1)

method TestNestedLet() {
  var x := Level2(5, Level1(3));

  var Level2(u, Level1(v)) := x;
}


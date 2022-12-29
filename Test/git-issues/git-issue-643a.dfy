// RUN: %baredafny verify %args "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
   expect false, "fails";
}

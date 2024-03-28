// RUN: %verify "%s" > "%t"
// RUN: ! %dafny /noVerify /compile:4 --target cs "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target java "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target js "%s" >> "%t"
// RUN: ! %dafny /noVerify /compile:4 --target go "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
   expect false, "fails";
}

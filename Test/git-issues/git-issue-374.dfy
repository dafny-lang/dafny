// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: sed -e 'sx\\x/x' < "%t" > "%t"2
// RUN: %diff "%s.expect" "%t"2

class C {
  constructor(ghost x: int)
  {
  }
}

function f() : int { 0 }

method main() {
  var c := new C(f());
}


// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  const i: nat := 1

  class X {}
}

module B {
  const i: nat := 2

  module X {
    const i: nat := 3
  }
}

method Main(){
  print A.i, " ", B.i, " ", B.X.i, "\n";
}

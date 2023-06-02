// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

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

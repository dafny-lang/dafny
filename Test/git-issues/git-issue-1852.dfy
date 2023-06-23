// RUN: %testDafnyForEachCompiler "%s" -- --relax-definite-assignment

module A {
  export
    reveals F, G

  ghost function G(): int { 5 }

  function F(): int {
    G()
  } by method {
    return 5;
  }
}

module B {
  export
    provides F

  ghost function G(): int { 5 }

  function F(): int {
    G()
  } by method {
    return 5;
  }
}

module Client {
  import A
  import B

  method Main() {
    // Test that A.F and B.F are both non-ghost here
    print A.F(), " ", B.F(), "\n"; // 5 5
  }
}

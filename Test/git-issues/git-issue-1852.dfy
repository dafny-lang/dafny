// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  export
    reveals F, G

  function G(): int { 5 }

  function F(): int {
    G()
  } by method {
    return 5;
  }
}

module B {
  export
    provides F

  function G(): int { 5 }

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

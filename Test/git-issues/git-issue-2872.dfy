// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /spillTargetCode:2 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module {:options "/functionSyntax:4"} Function4Syntax {

  method Main() {
    print F(2, 5, 9)(), "\n"; // 11
  }

  function F(a: int, ghost b: int, c: int): () -> int
  {
    () => G(a, b, c)
  }

  function G(a: int, ghost b: int, c: int): int {
    a + c
  }
}

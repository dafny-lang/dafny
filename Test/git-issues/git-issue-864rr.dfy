// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// Tests the resolution of the refinement parent -- that it ignores
// local declarations.
module A {
  const a := 10
}

module B refines A { // ignore the submodule A, use the top-level A
  module A {
    const a := 30
  }
  method Main() {
    assert a == 10; // true
    expect a == 10; // check it at runtime
    print "OK\n";
  }
}

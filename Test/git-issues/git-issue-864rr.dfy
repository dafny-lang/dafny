// RUN: %testDafnyForEachCompiler "%s"

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

// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

module A {
  datatype Wrapper = Wrap(val: int)
}

module B {
  datatype Wrapper = Wrap
}

module Main {
  import opened A
  import B

  method Main() {
    var Wrap(x) := Wrap(0);
    expect x == 0;
  }
}

// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism --general-traits=legacy "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Origin.Imported {
  trait {:termination false} SuperTrait {
    method X()
  }
}
module Importing {
  import Origin.Imported
  class TheClass extends Imported.SuperTrait {
    var x: int
    constructor() {
      x := 0;
    }
    method X() {
      print "ok";
    }
  }
}

newtype Index = x: int | 0 <= x < 3
method Main() {
  var dummy := new Importing.TheClass();
  dummy.X();
  var intWrappers := new Importing.TheClass[3]((i: int) requires 0 <= i < 3 => dummy);
  var intWrappers2 := new Importing.TheClass[3, 3]((i: int, j: int)
    reads intWrappers requires 0 <= i < 3 => intWrappers[i]);
  var index := 1 as Index;
  expect intWrappers[index] == intWrappers2[1, 1];
}

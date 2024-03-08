// RUN: %baredafny build %args -t:lib "%S/Inputs/internalLibrary.dfy" > "%t"
// RUN: %baredafny build %args -t:lib "%s" "%S/Inputs/internalLibrary.doo" >> "%t"
// RUN: %baredafny run %args MergeDooFiles.doo >> "%t"
// RUN: %diff "%s.expect" "%t"

module App {
  import InternalLibrary

  method Main() {
    InternalLibrary.Greet("world");
  }
}
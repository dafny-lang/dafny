// RUN: %verify --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Class {
  trait Parent { }

  class Record extends Parent {}

  function Pick(b: bool, r: Record, d: Parent): Parent {
    if b then r else d
  }

  method Select(b: bool, r: Record, d: Parent) returns (p: Parent) {
    p := if b then r else d;
  }
}

module Datatype {
  trait Parent { }

  datatype Record extends Parent = Record

  function Pick(b: bool, r: Record, d: Parent): Parent {
    if b then r else d
  }

  method Select(b: bool, r: Record, d: Parent) returns (p: Parent) {
    p := if b then r else d;
  }
}

// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module ValueType {
  export S
    provides Value, Gimmie

  type Value = s: seq<bool> | |s| <= 10

  function method Gimmie(): Value {
    [true, true, false]
  }
}

module UI {
  import ValueType`S

  datatype Op = GetOp(value: ValueType.Value)
}

import V = ValueType`S

method Main() {
  var op := UI.GetOp(V.Gimmie());
  print op, "\n";
}

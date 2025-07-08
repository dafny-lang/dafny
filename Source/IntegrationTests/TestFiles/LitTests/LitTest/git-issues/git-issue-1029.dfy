// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

module ValueType {
  export S
    provides Value, Gimmie

  type Value = s: seq<bool> | |s| <= 10

  function Gimmie(): Value {
    [true, true, false]
  }
}

module UI {
  import ValueType`S

  datatype Op = GetOp(value: ValueType.Value)
  datatype Op2 = GetOps(v: ValueType.Value, v': ValueType.Value)
}

import V = ValueType`S

method Main() {
  var op := UI.GetOp(V.Gimmie());
  var op2 := UI.GetOps(V.Gimmie(), V.Gimmie());
  print op, " ", op2, "\n"; // [true, true, false] Op2([true, true, false], [true, true, false])
}

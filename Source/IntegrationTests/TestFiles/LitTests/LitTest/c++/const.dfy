// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

module Holder {
  const x:bool := false
}

module User {
  import opened Holder

  method Use() {
    var b := x;
  }

  method Main() {
    Use();
  }
}

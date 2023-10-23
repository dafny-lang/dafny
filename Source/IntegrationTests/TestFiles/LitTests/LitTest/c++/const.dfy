// RUN: %testDafnyForEachCompiler "%s" --refresh-exit-code=0 -- --relax-definite-assignment --spill-translation --unicode-char:false

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

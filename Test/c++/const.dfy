// RUN: %baredafny run %args --target=cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

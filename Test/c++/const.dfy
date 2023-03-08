// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp /unicodeChar:0 "%s" > "%t"
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

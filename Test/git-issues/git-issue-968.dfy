// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype DT<T(0)> = Make | Create {
  static const b := 30
  static const t: T
}

method Test0() {
//  var x := DT<int>.b;  // this works
  var y := DT.b;  // this causes a crash, but it should just have complained that "DT" is underspecified
}


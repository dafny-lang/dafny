// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype DT<T(0)> = Make | Create {
  static const b := 30
  static const t: T
}

method Test0() {
  var x := DT<int>.b;  // this works
  var y := DT.b;  // this used to crash, because y had a known type but
                  // the type parameter of DT did not, which made it past
                  // Resolution but crashed in Translation
}


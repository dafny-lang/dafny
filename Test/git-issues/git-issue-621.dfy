// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module M {
  export provides D, MyData

  datatype D = D1 | D2

  const MyData : D := D1
}

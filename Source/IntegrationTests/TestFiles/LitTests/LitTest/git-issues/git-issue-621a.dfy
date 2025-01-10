// RUN: %testDafnyForEachResolver "%s"


module M {
  export provides D, MyData
  datatype D = D1 | D2
  const MyData : D := D1  // OK even though in the export view, MyData does not have an initializer
}


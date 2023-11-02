// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module M {
  export provides D, MyData
  datatype D = D1 | D2
  const MyData : D := D1  // OK even though in the export view, MyData does not have an initializer
}

module M1 {
  import M
  const MyData : M.D  // Error - no initializer since M1 does not see D's definition
}


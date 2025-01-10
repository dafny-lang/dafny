// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


module A {
  newtype int0 = x | true // newtype's base type is not fully determined; add an explicit type for 'x'
}

module B {
  newtype int0 = y | true
  const x: int0 := 0 // type for constant 'x' is 'int0', but its initialization value type is 'int'
}

module C {
  type int0 = x | true // subset type's base type is not fully determined; add an explicit type for 'x'
}

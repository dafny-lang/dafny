// RUN: %exits-with 2 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  newtype int0 = x | true // newtype's base type is not fully determined; add an explicit type for 'x'
}

module B {
  newtype int0 = x | true
  const x: int0 := 0; // type for constant 'x' is 'int0', but its initialization value type is 'int'
}


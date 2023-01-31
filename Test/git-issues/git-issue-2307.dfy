// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  newtype int0 = x: int | true
  type int1 = x: int0 | true

  const x: int0 := 0;
  const y: int1 := 0 as int1;
  // It was once the case that Dafny inferred the type of 0 in the next line as 'int', which is bad.
  const z: int1 := 0;
}

module B {
  newtype int0 = int
  type int1 = x: int0 | true

  const x: int0 := 0;
  const y: int1 := 0 as int1;
  // It was once the case that Dafny inferred the type of 0 in the next line as 'int', which is bad.
  const z: int1 := 0;
}

module C {
  newtype real0 = x: real | true
  type real1 = x: real0 | true

  const x: real0 := 0.0;
  const y: real1 := 0.0 as real1;
  // It was once the case that Dafny inferred the type of 0.0 in the next line as 'real', which is bad.
  const z: real1 := 0.0;
}

module D {
  newtype real0 = real
  type real1 = x: real0 | true

  const x: real0 := 0.0;
  const y: real1 := 0.0 as real1;
  // It was once the case that Dafny inferred the type of 0.0 in the next line as 'real', which is bad.
  const z: real1 := 0.0;
}

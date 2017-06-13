// RUN: %dafny  /compile:0  "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module A {
  const one:int := 1;
  const two:int := 2.5;   // error: type does not match
  const three:int := 3;
  const four:int := three + one;
  const five:int := six - one;  // error: cycle five -> six
  const six: int := five + one;
}

module B {
  class Class {
    const a: int := 10
    static function method G(): int
    {
      a  // error: "a" is an instance field, but G() is static
    }
  }
}

module C {
  ghost const x: int := 10
  class Class {
    ghost const y: int := 20
    function method F(): int
    {
      x +  // error: "x" is ghost
      y  // error: "y" is ghost
    }
  }
}


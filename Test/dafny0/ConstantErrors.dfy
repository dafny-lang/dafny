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

module B {  // non-static const's
  class Class {
    const a: int := 10
    static function method G(): int
    {
      a  // error: "a" is an instance field, but G() is static
    }
  }
}

module C {  // ghost const's
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

module D {  // const's with inferred types
  const pi := 3.14
  const ten := 10  // this type should be "int", not "SmallInt"
  
  newtype SmallInt = x | 0 <= x < 100
  method M() returns (sm: SmallInt) {
    sm := ten;  // error: "int" is not assignable to "Smallint"
  }
  
  method R() returns (r: real) {
    r := pi;
  }
}

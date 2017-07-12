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

// ---------- traits --------------------

module E {
  newtype Six = x | 6 <= x witness 6

  trait Trait {
    const x0: Six
    const x1: Six := 7
    const x2: Six
    const x3: Six := 8

    static const y: Six := 10
  }

  class Class extends Trait {
    const x0: Six  // error: not allowed to declare const
    const x1: Six := 7  // error: not allowed to declare const
    const x2: Six  // error: not allowed to declare const
    const x3: Six  // error: not allowed to declare const
  
    method Test() {
      print x0, " ", x1, " ", x2, "\n";
      print y, "\n";
    }
  }
}

// ---------- instanced-based initialization --------

module F {
  newtype Six = x | 6 <= x witness 6

  trait Trait {
    const x0: Six
    const x1: Six := 7
  }
  
  class InstanceInit extends Trait {
    const y2: Six
    const y3: Six := 12

    constructor (u: int)
      requires 10 <= u
    {
      x0 := 80;
      x1 := 100;  // error: cannot set a const whose declaration has an initial value
      y2 := 77 + y3;
      y3 := 110;  // error: cannot set a const whose declaration has an initial value
      new;
      x0, x1, y2, y3 := 50, 50, 50, 50;  // error (x4): cannot set const's after "new;"
    }
  }
}

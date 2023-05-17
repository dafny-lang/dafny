// RUN: %exits-with 2 %dafny /compile:0 /traitsReferences:1 "%s" > "%t"
// RUN: %exits-with 2 %dafny /compile:0 /traitsReferences:0 "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

module Tests {
  module M {
    trait {:termination false} MX { }
    trait {:termination false} MY extends object { }
    trait {:termination false} MZ extends MX, MY { }
  }

  trait Z extends Q { }
  trait Q { }
  trait A extends Z, object { }
  trait B extends A { }
  trait C extends A { }
  trait D extends B, C { }

  trait E extends M.MX { }
  trait F extends M.MY { }
  trait G extends M.MZ { }

  class MyClassA extends C, object, D { }
  class MyClassB extends C, D { }
  class MyClassC { }

  method Tests() {
    var mx: M.MX?; // error: no type MX?
    var my: M.MY?;
    var mz: M.MZ?;

    var z: Z?; // error: no type Z?
    var q: Q?; // error: no type Q?
    var a: A?;
    var b: B?;
    var c: C?;
    var d: D?;

    var e: E?; // error: no type E?
    var f: F?;
    var g: G?;

    var ca: MyClassA?;
    var cb: MyClassB?;
    var cc: MyClassC?;
  }
}

module MutableFields {
  datatype Dt<A> = Blue | Bucket(diameter: real) | Business(trendy: bool, a: A)
  {
    var x: int  // error: mutable fields not allowed in datatypes
  }
  newtype Pos = x | 0 < x witness 1
  {
    var x: int  // error: mutable fields not allowed in datatypes
  }
  type Opaque {
    var x: int  // error: mutable fields not allowed in datatypes
  }
  class Class {
    var x: int
  }
  trait NonReferenceTrait {
    var x: int  // error: mutable fields not allowed in non-reference trait types
  }
  trait ReferenceTrait extends object {
    var x: int
  }
  trait AnotherReferenceTrait extends ReferenceTrait {
    var y: int
  }
}

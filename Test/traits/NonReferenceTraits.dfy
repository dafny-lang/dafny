// RUN: %exits-with 2 %dafny /compile:0 /traitsReferences:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

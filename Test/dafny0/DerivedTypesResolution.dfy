// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module Cycle {
  type MySynonym = MyNewType  // error: a cycle
  type MyNewType = new MyIntegerType_WellSupposedly
  type MyIntegerType_WellSupposedly = MySynonym
}

module MustBeNumeric {
  datatype List<T> = Nil | Cons(T, List)
  type NewDatatype = new List<int>  // error: base type must be numeric based
}

module Goodies {
  type int32 = new int
  type posReal = new real
  type int8 = new int32

  method M()
  {
    var k8 := new int8[100];
    var s: set<int32>;
    var x: posReal;
    var y: posReal;
  }
}

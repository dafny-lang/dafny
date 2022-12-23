// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" ExternDefs.h > "%t"
// RUN: %diff "%s.expect" "%t"

module {:extern "Extern"} Extern {
  newtype uint64 = i:int | 0 <= i < 0x10000000000000000

  method {:extern "Extern", "newArrayFill"} newArrayFill<T>(n: uint64, t: T) returns (ar: array<T>)

  type {:extern "struct"} state

  class {:extern} ExternClass {
    constructor {:extern "Extern", "ExternClass"}()
    method {:extern "Extern", "my_method0"} my_method0(a:uint64) returns (b:bool)
    method {:extern "Extern", "my_method1"} my_method1(c:uint64) returns (d:bool)
  }

  class {:extern} ExternClass2 {
    constructor {:extern "Extern", "ExternClass2"}(x:uint64)
  }
}

module TestMod {
  import opened Extern

  // Test a templated extern declaration
  type {:extern "struct"} DestructorFunction<A>

  class C {
    var s:state;

    constructor (i:state) {
      this.s := i;
    }
  }

  class D {
    var s:uint64;

    constructor (i:uint64) {
      this.s := i;
    }
  }

  method TestClass(e:ExternClass) {
    var x := e.my_method0(0);
    var y := e.my_method1(1);
    print x, y, "\n";
  }

  method TestExternClass2() {
    var x := new ExternClass2(42);
  }

  method Main() {
    var a:array<uint64> := newArrayFill(5, 42);
    var d := new D(21);
    var b:array<D> := newArrayFill(3, d);

    var e:ExternClass := new ExternClass();
    TestClass(e);
  }
}

// RUN: %verify "%s" > "%t"
// RUN: %run --no-verify --target cs "%s" --input %S/Extern2.cs >> "%t"
// RUN: %run --no-verify --target js "%s" --input %S/Extern3.js >> "%t"
// RUN: %run --no-verify --target go "%s" --input %S/Extern4.go >> "%t"
// RUN: %run --no-verify --target java "%s" --input %S/SingletonOptimization.java --input %S/LibClass.java --input %S/OtherClass.java --input %S/AllDafny.java --input %S/Mixed.java --input %S/AllExtern.java >> "%t"
// RUN: %run --no-verify --target py "%s" --input %S/Extern5.py >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  print "Hello\n";
  var x, y := Library.LibClass.CallMeInt(30);
  var z := Library.LibClass.CallMeNative(44, true);
  var w := Library.LibClass.CallMeInAnotherClass();
  print x, " ", y, " ", z, " ", w, "\n";

  Library.AllDafny.M();
  Library.Mixed.M();
  print Library.Mixed.F(), "\n";
  var m := new Library.Mixed();
  m.IM();
  print m.IF(), "\n";
  Library.AllExtern.P();
  assert Library.AllDafny.Seven() == Library.Mixed.Seven() == Library.AllExtern.Seven();
  var maybeInt := Library.AllExtern.MaybeInt();
  print maybeInt, "\n";
  var intPair := Library.AllExtern.IntPair();
  print intPair, "\n";

  var singleton := Library.SingletonOptimization.SingletonTuple((ghost 10, 2));
  assert singleton.0 == 3;
  var noWrapper := Library.SingletonOptimization.NoWrapper(Library.ErasableWrapper(2));
  assert noWrapper.x == 3;
  var ghostWrapper := Library.SingletonOptimization.GhostWrapper(Library.Something(2));
  assert ghostWrapper.x == 3;
  print singleton.0, " ", noWrapper.x, " ", ghostWrapper.x, "\n"; // 3 3 3
}

module Wrappers {
  datatype Option<T> = Some(value: T) | None
  datatype Pair<A, B> = Pair(first: A, second: B)
}

module {:extern "Library"} Library {
  import opened Wrappers

  newtype MyInt = x | -100 <= x < 0x8000_0000
  
  class {:extern "LibClass"} LibClass {
    static method {:extern} CallMeInt(x: int) returns (y: int, z: int)
    static method {:extern} CallMeNative(x: MyInt, b: bool) returns (y: MyInt)
    static method {:axiom} {:extern "Library.OtherClass", "CallMe"} CallMeInAnotherClass() returns (w : object)
  }

  class {:extern} AllDafny {
    static function Seven(): int { 7 }
    static method M() { print "AllDafny.M\n"; }
  }
  class {:extern} Mixed {
    constructor() { }
    static function Seven(): int { 7 }
    static method M() { print "Extern static method says: "; P(); }
    static method {:extern} P()
    method IM() { print "Extern instance method says: "; IP(); }
    method {:extern} IP()
    static function F() : int { 1000 + G() }
    static function {:extern} G() : int
    function IF() : int { 2000 + IG() }
    function {:extern} IG() : int
  }
  class {:extern} AllExtern {
    static ghost function Seven(): int { 7 }
    static method {:extern} P()
    static function {:extern} MaybeInt(): Option<int>
    static function {:extern} IntPair(): Pair<int, int>
  }

  datatype ErasableWrapper = ErasableWrapper(x: MyInt)

  datatype Ghost<X> = ghost Uninitialized | Something(x: X)

  class {:extern} SingletonOptimization {
    // The in-parameter and out-parameter of these methods are optimized to just an "MyInt"
    static method {:axiom} {:extern} SingletonTuple(a: (ghost MyInt, MyInt)) returns (b: (MyInt, ghost MyInt, ghost MyInt))
      requires a.1 < 0x7fff_ffff
      ensures b.0 == a.1 + 1
    static method {:axiom} {:extern} NoWrapper(a: ErasableWrapper) returns (b: ErasableWrapper)
      requires a.x < 0x7fff_ffff
      ensures b.x == a.x + 1
    static method {:axiom} {:extern} GhostWrapper(a: Ghost<MyInt>) returns (b: Ghost<MyInt>)
      requires a.Something? && a.x < 0x7fff_ffff
      ensures b.Something? && b.x == a.x + 1
  }
}

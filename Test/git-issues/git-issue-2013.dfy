// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:py "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"


method Main() {
  TestTraits();
  TestSiblings();
  TestException();
  MoreTests.Test();
  Conveyance.Test();
  Regression.Test();
}

// ----- reference types -----

datatype Dt<+U> = Dt(u: U)

trait Tr {
  var y: int
}

class Cl extends Tr {
  constructor () {
    y := 15;
  }
}

method Print(e: Dt<Cl>) {
  print e.u.y, "\n";
}

method CreateDtForTrait(e: Dt<Cl>) returns (d: Dt<Tr>)
  ensures d.u == e.u
{
  d := e; // upcast
}

method TestTraits() {
  var cl := new Cl();
  var e: Dt<Cl> := Dt(cl);
  var d: Dt<Tr> := CreateDtForTrait(e);
  cl.y := cl.y + 1;
  var f: Dt<Cl> := d; // downcast

  Print(f); // 16
  Print(e); // 16
}

// ----- sibling types -----

type Even = x | x % 2 == 0

method TestSiblings() {
  // downcasts
  var a: Dt<int> := Dt(10);
  var b: Dt<nat> := a;
  var c: Dt<Even> := a;

  // upcasts
  b := Dt(11);
  c := Dt(12);
  a := b;
  a := c;

  // sideway casts
  b := Dt(20);
  c := b;
  c := Dt(30);
  b := c;

  print a, " ", b, " ", c, "\n"; // Dt.Dt(12) Dt.Dt(30) Dt.Dt(30)
}

// ----- Result -----

datatype Result<+T, +R> = | Success(value: T) | Failure(error: R)

trait Exception {}

class MyClassException extends Exception { }

class MyClass {
  const error: Exception

  constructor () {
    error := new MyClassException;
  }

  function Foo(u: int): Result<int, Exception> {
    if u < 8 then
      Success(8)
    else
      Failure(error)
  }
}

method TestException() {
  var c := new MyClass();
  print c.Foo(2), " ", c.Foo(22), "\n"; // Result.Success(8) Result.Failure(_module.MyClassException)
}

module MoreTests {
  type Even = x | x % 2 == 0

  datatype Dt<T> = Make(T)
  datatype DtCovariant<+T> = MakeCovariant(T)

  trait Z { }
  trait X extends Z { }
  trait Y extends Z { }
  class C extends X, Y { }

  method Test() {
    var c := new C;

    var s: set<int> := {100};
    var t: set<nat> := s;
    var u: set<Even> := s;
    t := u;
    u := t;
    s := u;
    s := t;
    print s, " ", t, " ", u, "\n"; // {100} {100} {100}

    var S: set<Z> := {c};
    var T: set<X> := S;
    var U: set<Y> := S;
    T := U;
    U := T;
    S := U;
    S := T;
    print S, " ", T, " ", U, "\n"; // {_module.C} {_module.C} {_module.C}

    // The assignments in the following example don't need covariance of Dt, because
    // Dafny checks that the value with its payload is suitable for the target type.
    var k: Dt<int> := Make(100);
    var m: Dt<nat> := k;
    var n: Dt<Even> := k;
    m := n;
    n := m;
    k := m;
    k := n;
    print k, " ", m, " ", n, "\n"; // Dt.Make(100) Dt.Make(100) Dt.Make(100)

    var K: DtCovariant<Z> := MakeCovariant(c);
    var M: DtCovariant<X> := K;
    var N: DtCovariant<Y> := K;
    M := var u: DtCovariant<Z> := N; u; // like M := N, but allowed by Dafny's type system
    N := var u: DtCovariant<Z> := M; u; // like N := M, but allowed by Dafny's type system
    print K, " ", M, " ", N, "\n"; // DtCovariant.MakeCovariant(_module.C) DtCovariant.MakeCovariant(_module.C) DtCovariant.MakeCovariant(_module.C)
  }
}

// ----- Vehicle -----

module Conveyance {
  trait Vehicle {
  }
  class Car extends Vehicle {
    constructor() {}
  }

  trait Error {
  }
  class FlatTireError extends Error {
    constructor() {}
  }

  datatype NonVariantResult<T, E> = NVSuccess(value: T) | NVFailure(error: E)
  datatype CovariantResult<+T, +E> = CVSuccess(value: T) | CVFailure(error: E)

  method Test() {
    var myCar: Car := new Car();
    var error: Error := new FlatTireError();

    var cvSuccess: CovariantResult<Vehicle, Error> := CVSuccess(myCar);
    var cvFailure: CovariantResult<Vehicle, Error> := CVFailure(error);

    var nvSuccess: NonVariantResult<Vehicle, Error> := NVSuccess(myCar);
    var nvFailure: NonVariantResult<Vehicle, Error> := NVFailure(error);

    // This was and remains just fine
    var nvCarSuccess: NonVariantResult<Car, Error> := NVSuccess(myCar);
    // The following would not be type correct for the non-variant NonVariantResult:
    //     var nvVehicleSuccess: NonVariantResult<Vehicle, Error> := nvCarSuccess; // RHS (...) not assignable to LHS (...)

    // Once, the following was not support for the Java target, but now it is
    var cvCarSuccess: CovariantResult<Car, Error> := CVSuccess(myCar);
    var cvVehicleSuccess: CovariantResult<Vehicle, Error> := cvCarSuccess;

    print nvCarSuccess, " ", cvCarSuccess, "\n"; // NonVariantResult.NVSuccess(_module.Car) CovariantResult.CVSuccess(_module.Car)
  }
}

// ----- Regression test -----

module Regression {
  module M {
    // A previous bug was that the following declaration was not exported correctly (in several compilers).
    codatatype Stream<T> = Next(shead: T, stail: Stream)
  }

  function CoUp(n: int, b: bool): M.Stream<int>
  {
    if b then
      CoUp(n, false)  // recursive, not co-recursive, call
    else
      M.Next(n, CoUp(n+1, true))  // CoUp is co-recursive call
  }

  method Test(){
    print CoUp(0, false), "\n";
  }
}

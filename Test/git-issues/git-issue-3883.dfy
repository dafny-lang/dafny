// RUN: %testDafnyForEachCompiler "%s"

type MyType<T> = x: T | true witness *
type MyInt<T> = x: int | true witness *

method Main() {
  var a: MyType<int> := 13; // NOTE: this used to not verify
  TestMyTest(a, 14); // 13 14 // NOTE: this used to crash the resolved
  var b: MyType<bool> := true;
  TestMyTest(b, false); // true false
  print a, " ", b, "\n"; // 13 true

  var c: MyInt<object> := 18;
  var d: MyInt<bv19> := 19;
  print c, " ", d, "\n"; // 18 19

  TestOthers();

  DoIt<real>();

  Arrows();

  MoreTests.Placebo();
}

method TestMyTest<U>(m: MyType<U>, u: U) {
  var w: U := u;
  var n: MyType<U> := m;
  w := m;
  n := u;
  print m, " ", u, "\n";
}

datatype ABC<X> = MakeABC(X)
datatype XYZ<A(0)> = MakeXYZ(A)
type SSS<Y> = s: seq<Y> | |s| <= 10

method TestOthers() {
  var a := MakeABC(10);
  var b := MakeXYZ(null);
  var c: SSS<bool> := [false, true, false];
  print a, " ", b, " ", c, "\n"; // 10 null [false, true, false]
}

type ST0<T, U(0)> = x: int | x % 5 == 1 witness 16
type ST1<T, U(0)> = x: int | (if var m: map<T,U> := map[]; m == map[] then 0 else 8) <= x

method DoIt<X(0)>() {
  var t0: ST0<int, X>;
  var t1: ST1<int, X>;
  Print(t0, " "); // 16-16
  Print(t1, "\n"); // 0-0
}

method Print<X(0)>(x: X, suffix: string) {
  var y: X;
  print x, "-", y, suffix;
}

type pos = x | 1 <= x witness 9
type Fn<R(0)> = f: int -> R | true witness *

method Arrows() {
  var f: Fn<int>;
  var g: Fn<pos>;
}

module MoreTests {
  datatype BSingle<X> = BPlop(bool)
  type BMyTypeWrapper<T> = x: BSingle<T> | true witness *
  datatype BD = BD(BMyTypeWrapper<int>)

  datatype XSingle<X> = XPlop(X)
  type XMyTypeWrapper<T> = x: XSingle<T> | true witness *
  datatype XD = XD(XMyTypeWrapper<int>)

  datatype IntCell = IntCell(int)
  type ConstrainedIntCell = c: IntCell | true witness *
  type GurgleInt = ConstrainedIntCell
  datatype WrappedInt = WrappedInt(GurgleInt)
  type MyTypeAroundInt<T> = x: WrappedInt | true witness *

  datatype UCell<U> = UCell(U)
  type ConstrainedUCell<U> = u: UCell<U> | true witness *
  type GurgleU<U> = ConstrainedUCell<U>
  datatype WrappedU<U> = WrappedU(GurgleU<U>)
  type MyTypeAroundU<U> = x: WrappedU<U> | true witness *

  method Placebo() {
    var a: XSingle<int>;
    var b: XMyTypeWrapper<int>;
    var c: XD;
  }
}

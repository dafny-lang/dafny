// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
trait SuperTrait {
  function GetBool(): bool
}
trait DatatypeOps<T> extends SuperTrait {
  function GetInt(): int
  function GetBool(): bool {
    GetInt() % 2 == 0
  }
  function ChooseAmong(a: T, b: T): T {
    if GetBool() then a else b
  }
  method ChooseAmongMethod(a: T, b: T) returns (c: T) {
    if GetBool() {
      return a;
    } else {
      c := b;
    }
  }
}

datatype {:rust_rc false} ADatatype extends DatatypeOps<int> = ADatatype(i: int) {
  function AsDatatypeOps(): DatatypeOps<int> {
    this as DatatypeOps<int>
  }
  function GetInt(): int { i }
}

method StaticWithGenerics<T>(c: bool, a: T, b: T) returns (t: T){
  if c {
    t := a;
  } else {
    t := b;
  }
}
function StaticWithGenericsFn<T>(c: bool, a: T, b: T): (t: T){
  if c then a else b
}

datatype TW<T> = TW(d: DatatypeOps<T>) {}

method Main() {
  var x := ADatatype(2);
  expect x.GetInt() == 2;
  expect x.GetBool() == true;
  expect x.ChooseAmong(8, 9) == 8;
  var xm := x.ChooseAmongMethod(8, 9);
  expect xm == 8;
  var y := ADatatype(3);
  expect y.GetInt() == 3;
  expect y.GetBool() == false;
  expect y.ChooseAmong(8, 9) == 9;
  var ym := y.ChooseAmongMethod(8, 9);
  expect ym == 9;
  var x1 := x.AsDatatypeOps(); // Dynamic dispatch now.
  expect x1.GetInt() == 2;
  expect x1.GetBool() == true;
  expect x1.ChooseAmong(8, 9) == 8;
  var x1m := x1.ChooseAmongMethod(8, 9);
  expect x1m == 8;
  var y1 := y.AsDatatypeOps();
  expect y1.GetInt() == 3;
  expect y1.GetBool() == false;
  expect y1.ChooseAmong(8, 9) == 9;
  var y1m := y1.ChooseAmongMethod(8, 9);
  expect y1m == 9;
  var zy := y as SuperTrait;
  var zx := x as SuperTrait;
  expect zx.GetBool();
  expect !zy.GetBool();
  var xory1a := StaticWithGenerics(true, x1, y1);
  var xory1b := StaticWithGenerics(false, x1, y1);
  var xory1c := StaticWithGenericsFn(true, x1, y1);
  var xory1d := StaticWithGenericsFn(false, x1, y1);
  expect TW(xory1a) == TW(x1) == TW(xory1c) != TW(y1); // If not wrapped, Dafny complains
  expect TW(xory1b) == TW(y1) == TW(xory1d) != TW(x1);
  print x1, "\n"; // Ensure we can print even if behind trait
  print TW(x1) == TW(x1), "\n"; // True
  print TW(x1) == TW(y1), "\n"; // False
  print "Main passed all the tests";
}
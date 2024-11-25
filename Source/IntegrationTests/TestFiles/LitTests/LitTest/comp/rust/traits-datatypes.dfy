// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --type-system-refresh --general-traits=datatype "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

trait DatatypeOps<T> {
  function GetInt(): int
  function GetBool(): bool {
    GetInt() % 2 == 0
  }
  function ChooseAmong(a: T, b: T): T {
    if GetBool() then a else b
  }
}

datatype {:rust_rc false} ADatatype extends DatatypeOps<int> = ADatatype(i: int) {
  function AsDatatypeOps(): DatatypeOps<int> {
    this as DatatypeOps<int>
  }
  function GetInt(): int { i }
}

method Main() {
  var x := ADatatype(2);
  expect x.GetInt() == 2;
  expect x.GetBool() == true;
  expect x.ChooseAmong(8, 9) == 8;
  var y := ADatatype(3);
  expect y.GetInt() == 3;
  expect y.GetBool() == false;
  expect x.ChooseAmong(8, 9) == 9;
  var x1 := x.AsDatatypeOps(); // Dynamic dispatch now.
  expect x1.GetInt() == 2;
  expect x1.GetBool() == true;
  expect x1.ChooseAmong(8, 9) == 8;
  var y1 := y.AsDatatypeOps();
  expect y1.GetInt() == 3;
  expect y1.GetBool() == false;
  expect y1.ChooseAmong(8, 9) == 9;
  print "Main passed all the tests";
}
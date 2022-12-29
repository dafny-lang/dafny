// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:cs "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:js "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:go "%s" >> "%t"
// RUN: %dafny /noVerify /compile:4 /compileTarget:java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

datatype Foo = R(v: int)

method m(f: Foo) returns (x: int) {
  x := 0;
  match f {
    case R(0) => x := 1;
    case R(1) => x := 2;
    case R(y) => x := -y;
  }
  assert f.v == 0 ==> x == 1;
  assert f.v == 1 ==> x == 2;
  assert f.v != 0 && f.v != 1 ==> x == -f.v;
}

const ZERO := 0
const ONE := 1

method m2(f: Foo) returns (x: int) {
  x := 0;
  match f {
    case R(ZERO) => x := 1;
    case R(ONE) => x := 2;
    case R(y) => x := -y;
  }
  assert f.v == 0 ==> x == 1;
  assert f.v == 1 ==> x == 2;
  assert f.v != 0 && f.v != 1 ==> x == -f.v;
}

method Main() {
  var x: int;
  x := m(R(1));
  expect x == 2;
  x := m2(R(1));
  expect x == 2;
}

datatype Cell<T> = Cell(value: T)

const X := 1
method q() {
  var c: Cell;  // note, type argument omitted; it will eventually be inferred
  match c {
    case Cell(X) => assert X == 1; // at this time, the type argument hasn't yet been inferred, but X is a const so it is not a variable
    case Cell(_) =>     // if X is a const, then this case is not redundant
  }
}

// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype Foo = R(v: int)

const ZERO := 0
const ONE := ZERO+1

method m2(f: Foo) {
  var x: int := 0;
  match f {
    case R(ZERO) => x := 1;
    case R(ONE) => x := 2; // ERROR - ONE not a literal
    case R(y) => x := -y;
  }
  assert f.v == 0 ==> x == 1;
  assert f.v == 1 ==> x == 2;
  assert f.v != 0 && f.v != 1 ==> x == -f.v;
}

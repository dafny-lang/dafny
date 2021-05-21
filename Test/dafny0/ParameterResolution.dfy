// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function method F(x: int, y: int, z: int): int

method M0() {
  var a0 := F(2, 3, 5);
  var a1 := F(2, y := 3, z := 5);
  var a2 := F(2, z := 5, y := 3);
  var a3 := F(x := 2, y := 3, z := 5);
  var a4 := F(y := 3, x := 2, z := 5);
  assert a0 == a1 == a2 == a3 == a4;
}

method M1() {
  var a0 := F(2, 3); // error: too few arguments
  var a1 := F(2, 3, 5, 7); // error: too many arguments
  var a2 := F(2, y := 3, y := 5); // error: repeated parameter y (and no z)
  var a3 := F(2, x := 5, y := 3); // error: repeated parameter x (and no z)
  var a4 := F(2, y := 3, 5); // error: positional argument follows named argument
}

datatype Record = Record(a: int, bool, c: real)

method M2() {
  var a0 := F(2, 3, xyz := 5); // error: no parameter of F is called 'xyz'
  var r0 := Record(2, true, 3.9);
  var r1 := Record(2, true, c := 3.9);
  var r2 := Record(2, c := 3.9); // error: too few arguments
  var r3 := Record(2, c := 3.9, a := 2); // error: 'a' already given positionally
}

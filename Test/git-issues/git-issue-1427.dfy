type T

method m(t1: T, t2: T) {
  var x := t1 == t2; // correctly gives error
}

datatype X = X(t: T)

method m2(x1: X, x2: X) {
  var y := x1 == x2; // doesn't error but should
}

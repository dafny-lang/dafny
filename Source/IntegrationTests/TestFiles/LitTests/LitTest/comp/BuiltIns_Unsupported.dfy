// RUN: %testDafnyForEachCompiler "%s"

method HasTuples() {
  var b := true;
  var has21 := (b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b,b);
}

method HasArrows() {
  var has17 := (x1: bool, x2: bool, x3: bool, x4: bool, x5: bool, x6: bool, x7: bool, x8: bool, x9: bool, x10: bool, x11: bool, x12: bool, x13: bool, x14: bool, x15: bool, x16: bool, x17: bool) => 42;
}

newtype byte = x: int | 0 <= x < 256

method HasArrays() {
  var n: byte := 0;
  var has17 := new bool[n,n,n,n,n,n,n,n,n,n,n,n,n,n,n,n,n];
}

method Main() {
  HasTuples();
  HasArrows();
  HasArrays();
}

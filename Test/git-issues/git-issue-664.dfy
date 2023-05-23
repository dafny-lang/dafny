// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  static const X: int
  static method M() { }
  static ghost function F(): int { 5 }
}

method TestClass(c: C) {
  if
  case true =>
    var x := (if 5/0 == 1 then c else c).X;  // error: receiver is not well-formed
  case true =>
    (if 5/0 == 2 then c else c).M();  // error: receiver is not well-formed
  case true =>
    var x := (if 5/0 == 3 then c else c).F();  // error: receiver is not well-formed
  case true =>
    var f := (if 5/0 == 4 then c else c).F;  // error: receiver is not well-formed
}

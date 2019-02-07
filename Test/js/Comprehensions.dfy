// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cs "%s" > "%t"
// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:js "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  AssignSuchThat();
  LetSuchThat();
  Quantifier();
  MapComprehension();
}

predicate method Thirteen(x: int) { x == 13 }
predicate method Even(y: int) { y % 2 == 1 }
function method FourMore(x: int): int { x + 4 }

method AssignSuchThat() {
  var x, y;
  assert Thirteen(13);
  x, y :| 12 <= x < y && Thirteen(x);
  print "x=", x, " y=", y, "\n";
  var b;
  x, b, y :| 12 <= x < y && Thirteen(x) && b;
  print "x=", x, " y=", y, " b=", if b then "yes" else "no", "\n";
}

method LetSuchThat() {
  assert Thirteen(13);
  var p := var x, y :| 12 <= x < y < 15 && Thirteen(x); (x, y);
  print "p=", p, "\n";
  var q := var x, b, y :| 12 <= x < y < 15 && Thirteen(x) && b; (x, y, if b then "yes" else "no");
  print "q=", q, "\n";
}

method Quantifier() {
  var s := [0, 1, 1, 2, 3, 5, 8, 13];
  print forall x :: x in s ==> x < 20, " ";  // true
  print forall x :: x in s ==> x < 10, "\n";  // false
  print exists x :: x in s && x == 3, " ";  // true
  print exists x :: x in s && x == 4, "\n";  // false
}

method MapComprehension() {
  // var m := map x,y | 12 <= x < y < 17 && Thirteen(x) && Even(y) :: x := y;
  var m := map x | 12 <= x < 15 :: x / 2;
  print m, "\n";
  m := map x | 12 <= x < 15 :: FourMore(x) := x;
  print m, "\n";
}

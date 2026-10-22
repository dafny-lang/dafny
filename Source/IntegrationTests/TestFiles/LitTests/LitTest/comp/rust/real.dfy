// NONUNIFORM: Rust-specific tests for real (literals, printing, conversions, Floor, hashing)
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Pos = r: real | r >= 0.0
newtype Small = i: int | 0 <= i < 100

method Main() {
  var a: real := 0.25;
  var b: real := -0.5;
  var c: real := 1.0 / 3.0;
  print a, " ", b, " ", c, " ", a + b, " ", a * 4.0, " ", a - b, " ", a / b, "\n";
  print 0.125, " ", 0.2, " ", 1.0 / 8.0, " ", 10.0, " ", 0.0, " ", -0.75, " ", 1.0 / 40.0, "\n";
  print a < b, " ", a <= a, " ", a == 1.0 / 4.0, " ", b > a, "\n";
  var i: int := 7;
  var r: real := i as real;
  var n: int := -7;
  print r, " ", n as real, " ", (r / 2.0).Floor, " ", (-r / 2.0).Floor, " ", (r * 2.0) as int, " ", (n as real / 2.0).Floor, "\n";
  var s: set<real> := {0.5, 1.0 / 2.0, 0.0, 0.5 - 0.5};
  var m: map<real, int> := map[0.5 := 1];
  print |s|, " ", (2.0 / 4.0) in m, "\n";
  var sq: seq<real> := [a, b];
  print sq, "\n";
  var p: Pos := 2.5;
  var k: Small := 7;
  var q: real := k as real;
  print p.Floor, " ", (p as real) * 2.0, " ", q / 2.0, " ", (q / 2.0).Floor as Small, " ", (q * 2.0) as Small, "\n";
}

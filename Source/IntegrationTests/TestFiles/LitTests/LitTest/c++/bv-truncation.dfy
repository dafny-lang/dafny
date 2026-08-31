// RUN: %testDafnyForEachCompiler "%s" -- --allow-deprecation --unicode-char false

// Regression test for bitvector-width truncation (issue #6512): the cpp backend
// left fixed-width bv8/bv16 arithmetic un-masked while cs/java/py truncated it.
// Runs on every backend so all must agree. Operations are inline: assigning to a
// bvN variable first would truncate on the cast and hide the bug. The results are
// printed and checked against the .expect file.

method Main() {
  // ---- bv8 ----
  var a: bv8 := 200;
  var b: bv8 := 100;
  print "bv8:\n";
  print "200 + 100 == ", a + b, "\n";
  print "100 - 200 == ", b - a, "\n";
  print "200 * 100 == ", a * b, "\n";
  print "!200 == ", !a, "\n";
  var x: bv8 := 0x81;
  print "0x81 << 1 == ", x << 1, "\n";

  // ---- bv16 (same thing, 16 bits) ----
  var c: bv16 := 50000;
  var d: bv16 := 40000;
  print "bv16:\n";
  print "50000 + 40000 == ", c + d, "\n";
  print "40000 - 50000 == ", d - c, "\n";
  print "50000 * 40000 == ", c * d, "\n";
  print "!50000 == ", !c, "\n";
  var y: bv16 := 0x8001;
  print "0x8001 << 1 == ", y << 1, "\n";
}

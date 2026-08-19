// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --unicode-char false

// Regression test for bitvector-width truncation (issue #6512): the cpp backend
// left fixed-width bv8/bv16 arithmetic un-masked while cs/java/py truncated it.
// Runs on every backend so all must agree. Comparisons are inline: assigning to a
// bvN variable first would truncate on the cast and hide the bug. Output is
// "ok"/"WRONG" so it self-checks.

method Main() {
  // ---- bv8 ----
  var a: bv8 := 200;
  var b: bv8 := 100;
  print "bv8 add: ", if (a + b) == 44  then "ok" else "WRONG", "\n";
  print "bv8 sub: ", if (b - a) == 156 then "ok" else "WRONG", "\n";
  print "bv8 mul: ", if (a * b) == 32  then "ok" else "WRONG", "\n";
  print "bv8 not: ", if (!a) == 55     then "ok" else "WRONG", "\n";
  // (x << 7) keeps only the LSB, so (x << 7) != 0 is "is x odd?"
  var x: bv8 := 0x02;
  print "bv8 lsb: ", if ((x << 7) != 0) == false then "ok" else "WRONG", "\n";

  // ---- bv16 (same thing, 16 bits) ----
  var c: bv16 := 50000;
  var d: bv16 := 40000;
  print "bv16 add: ", if (c + d) == 24464 then "ok" else "WRONG", "\n";
  print "bv16 sub: ", if (d - c) == 55536 then "ok" else "WRONG", "\n";
  print "bv16 mul: ", if (c * d) == 37888 then "ok" else "WRONG", "\n";
  print "bv16 not: ", if (!c) == 15535    then "ok" else "WRONG", "\n";
  var y: bv16 := 0x0002;
  print "bv16 lsb: ", if ((y << 15) != 0) == false then "ok" else "WRONG", "\n";
}

// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// An array is a reference, so it stays in a set when its elements change.

newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

method Main() {
  var a := new i32[1];
  var s := {a};
  a[0] := 2;
  print a in s, "\n";
}

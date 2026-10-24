// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// A new array's elements are values of its element type: here the default function and the witness.

newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000
type Pos = x: i32 | x > 0 witness 1

method Main() {
  var f := new (i32 -> i32)[2];
  var p := new Pos[2];
  print f[1](5), " ", p[1], "\n";
}

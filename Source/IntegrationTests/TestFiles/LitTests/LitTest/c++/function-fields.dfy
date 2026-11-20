// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// Datatypes with function-typed fields.

newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

datatype Op = Op(f: i32 -> i32, n: i32)
datatype Wrap = Wrap(f: i32 -> i32)
datatype Fs = Fs(a: array<i32 -> i32>)

method Main() {
  var inc: i32 -> i32 := n => if n < 0x7fff_ffff then n + 1 else n;

  // A field next to a function-typed one.
  var op := Op(inc, 1);
  print op.f(op.n), "\n";

  // A function as the only field.
  var w := Wrap(inc);
  print w.f(1), "\n";

  // Values holding different arrays of functions differ.
  var fs := new (i32 -> i32)[1];
  var gs := new (i32 -> i32)[1];
  print Fs(fs) == Fs(gs), " ", Fs(fs) == Fs(fs), "\n";
}

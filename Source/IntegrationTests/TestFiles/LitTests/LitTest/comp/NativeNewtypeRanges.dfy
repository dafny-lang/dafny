// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 --compilers cs,java,go,js,dfy,py,rs "%s" -- --allow-deprecation --unicode-char false
// C++ is left out because it does not compile ranges over native newtypes yet.

// Comprehensions over native newtypes, bounded by variables rather than literals.
// NativeNewtypeRangeForms.dfy has the forms that C++ does not support.

newtype u8 = x: int | 0 <= x < 0x100
newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000
newtype i64 = x: int | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
newtype u64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method Main() {
  var n: u64 := 4;
  var a := set i: u64 {:nowarn} | i < n;
  var b := set i: u64 {:nowarn} | i <= n;
  print |a|, " ", |b|, "\n";

  var c: i32, d: i32 := -2, 2;
  var e := set i: i32 {:nowarn} | c <= i < d;
  var f := set i: i32 {:nowarn} | d <= i < c;
  print |e|, " ", |f|, "\n";

  var lo: i64, hi: i64 := -0x7FFF_FFFF_FFFF_FFFF - 1, -0x7FFF_FFFF_FFFF_FFFE;
  var g := set i: i64 {:nowarn} | lo <= i <= hi;
  print |g|, " ", lo in g, "\n";

  var max: u64 := 0xFFFF_FFFF_FFFF_FFFF;
  var h := set i: u64 {:nowarn} | max - 2 <= i <= max;
  print |h|, " ", max in h, "\n";

  var mid: u64 := 0x7FFF_FFFF_FFFF_FFFF;
  var k := set i: u64 {:nowarn} | mid <= i < mid + 3;
  print |k|, "\n";

  var pairs := set i: u64, j: u64 | i < n && i <= j < n :: (i, j);
  print |pairs|, "\n";

  // Bounds that cannot be compared statically are compared at run time.
  var large: u64 := 0x1_0000_0000;
  var small := set i: u64 {:nowarn} | i < 10 && i < large;
  var three: u64 := 3;
  var x := set i: u64 {:nowarn} | i < 0x1_0000_0000_0000 && i < three;
  var y := set i: u64 {:nowarn} | i < large && i < three;
  var z := set i: u64 {:nowarn} | 2 <= i && three <= i && i < three + 3;
  print |small|, " ", |x|, " ", |y|, " ", |z|, "\n";

  // Bounds that leave the type: moving 50 across "<" gives j a lower bound of i - 49, and substituting j's bound
  // 206 or 128 gives i the upper bounds 206 + 50, 2 * 128, and (206 + 50) / 2.
  var shifted := set i: u8, j: u8 | 200 <= j < 206 && i < j + 50 :: (i, j);
  var doubled := set i: u8, j: u8 | 120 <= j < 128 && i < 2 * j :: (i, j);
  var halved := set i: u8, j: u8 | 200 <= j < 206 && i < (j + 50) / 2 :: (i, j);
  print |shifted|, " ", |doubled|, " ", |halved|, "\n";
  // Only u8's own lower bound keeps j from starting at i - 49, below 0.
  var clamped := set i: u8, j: u8 | i < 4 && j < 3 && i < j + 50 :: (i, j);
  print |clamped|, "\n";

  // Dafny's division rounds -1 / 2 down to -1, where C++'s rounds it to 0.
  var rounded := set j: i32, i: i32 | -20 <= j < 0 && j / 2 <= i < 5 :: (j, i);
  print |rounded|, "\n";
}

// NONUNIFORM: exercises the C++ backend's optional --bignum=boost mode (needs Boost
// headers), so it runs the cpp target directly rather than every compiler.
// RUN: %baredafny run --target cpp --bignum=boost --unicode-char false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Unbounded int, exact real and multiset on the C++ backend via --bignum=boost.
// Output must match the other Dafny backends (verified against C#).

newtype u64 = x: int | 0 <= x < 0x1_0000_0000_0000_0000

method Main() {
  // unbounded int: 10^30, well beyond 2^64
  var big := 1000000000000000000000000000000;
  print big, "\n";
  print big * big, "\n";

  // Euclidean div/mod with a negative dividend: -7 / 3 == -3, -7 % 3 == 2
  var a := -7;
  var b := 3;
  print a / b, " ", a % b, "\n";

  // exact reals: trailing-zero precision must match the other backends
  var x := 1.5;
  var y := 1.0;
  print x * y, "\n";        // 1.5
  print 0.75 - 0.25, "\n";  // 0.50
  print 0.5 + 0.5, "\n";    // 1.0
  print 1.0 / 3.0, "\n";    // (1.0 / 3.0)

  // real -> int floor
  print (-1.5).Floor, "\n";  // -2

  // multiset
  var m := multiset{1, 1, 2};
  print m[1], " ", m[2], "\n";   // 2 1
  print |m|, "\n";               // 3

  // A native unsigned value above 2^63 converted to real must stay positive
  // (not truncate through signed long).
  var u: u64 := 0x8000_0000_0000_0000;
  print u as real, "\n";         // 9223372036854775808.0

  // Equal multisets built in different orders must hash equal (multiset as a set
  // element / map key uses the hash).
  var s: set<multiset<int>> := {multiset{1, 2, 2}, multiset{2, 1, 2}};
  print |s|, "\n";               // 1
}

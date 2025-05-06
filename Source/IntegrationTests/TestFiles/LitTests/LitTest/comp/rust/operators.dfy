// NONUNIFORM: Rust-specific tests
// RUN: %baredafny run --target=rs --enforce-determinism "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
ghost const TWO_TO_THE_8:   int := 0x100
ghost const TWO_TO_THE_16:  int := 0x10000
ghost const TWO_TO_THE_32:  int := 0x1_00000000
ghost const TWO_TO_THE_64:  int := 0x1_00000000_00000000
ghost const TWO_TO_THE_128:  int := 0x1_00000000_00000000_00000000_00000000
newtype uint8  = x: int | 0 <= x < TWO_TO_THE_8
newtype uint16 = x: int | 0 <= x < TWO_TO_THE_16
newtype uint32 = x: int | 0 <= x < TWO_TO_THE_32
newtype uint64 = x: int | 0 <= x < TWO_TO_THE_64
newtype uint128 = x: int | 0 <= x < TWO_TO_THE_128

newtype int8  = x: int  | -0x80 <= x < 0x80
newtype int16 = x: int  | -0x8000 <= x < 0x8000
newtype int32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
newtype int64 = x: int  | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000
newtype int128 = x: int  | -0x8000_0000_0000_0000_0000_0000_0000_0000 <= x < 0x8000_0000_0000_0000_0000_0000_0000_0000

method TestLessEq() {
  var x64: uint64 := 8 as uint64;
  expect 8 as uint8 > 1 as uint8 + x64 as uint8;
  expect 9 as uint8 > 1 as uint8 * x64 as uint8;
}

method TestU8() {
  var o8: uint8 := 1 as uint8;
  var s8: uint8 := 2 as uint8;
  var w8: uint8 := 5 as uint8;
  var x8: uint8 := 8 as uint8;
  var y8: uint8 := 13 as uint8;
  var z8: uint8 := 21 as uint8;
  var m8: uint8 := 24 as uint8;
  var t8: uint8 := 16 as uint8;
  expect x8 + y8 == z8;
  expect y8 - x8 == w8;
  expect x8 as bv8 & y8 as bv8 == x8 as bv8;
  expect x8 as bv8 | y8 as bv8 == y8 as bv8;
  expect x8 as bv8 ^ y8 as bv8 == w8 as bv8;
  expect x8 * 3 == m8;
  expect x8 as bv8 >> s8 == s8 as bv8;
  expect x8 as bv8 << o8 == t8 as bv8;
  print "operators(u8) ";
}
method TestI8() {
  var o8: int8 := 1 as int8;
  var s8: int8 := 2 as int8;
  var w8: int8 := 5 as int8;
  var x8: int8 := 8 as int8;
  var y8: int8 := 13 as int8;
  var z8: int8 := 21 as int8;
  var m8: int8 := 24 as int8;
  var t8: int8 := 16 as int8;
  expect x8 + y8 == z8;
  expect x8 - y8 == -w8;
  expect x8 * 3 == m8;
  print "operators(i8) ";
}
method TestU16() {
  var o16: uint16 := 1 as uint16;
  var s16: uint16 := 2 as uint16;
  var w16: uint16 := 5 as uint16;
  var x16: uint16 := 8 as uint16;
  var y16: uint16 := 13 as uint16;
  var z16: uint16 := 21 as uint16;
  var m16: uint16 := 24 as uint16;
  var t16: uint16 := 16 as uint16;
  expect x16 + y16 == z16;
  expect y16 - x16 == w16;
  expect x16 as bv16 & y16 as bv16 == x16 as bv16;
  expect x16 as bv16 | y16 as bv16 == y16 as bv16;
  expect x16 as bv16 ^ y16 as bv16 == w16 as bv16;
  expect x16 * 3 == m16;
  expect x16 as bv16 >> s16 as bv16 == s16 as bv16;
  expect x16 as bv16 << o16 as bv16 == t16 as bv16;
  print "operators(u16) ";
}

method TestI16() {
  var o16: int16 := 1 as int16;
  var s16: int16 := 2 as int16;
  var w16: int16 := 5 as int16;
  var x16: int16 := 8 as int16;
  var y16: int16 := 13 as int16;
  var z16: int16 := 21 as int16;
  var m16: int16 := 24 as int16;
  var t16: int16 := 16 as int16;
  expect x16 + y16 == z16;
  expect x16 - y16 == -w16;
  expect x16 * 3 == m16;
  print "operators(i16) ";
}
method TestU32() {
  var o32: uint32 := 1 as uint32;
  var s32: uint32 := 2 as uint32;
  var w32: uint32 := 5 as uint32;
  var x32: uint32 := 8 as uint32;
  var y32: uint32 := 13 as uint32;
  var z32: uint32 := 21 as uint32;
  var m32: uint32 := 24 as uint32;
  var t32: uint32 := 16 as uint32;
  expect x32 + y32 == z32;
  expect y32 - x32 == w32;
  expect x32 as bv32 & y32 as bv32 == x32 as bv32;
  expect x32 as bv32 | y32 as bv32 == y32 as bv32;
  expect x32 as bv32 ^ y32 as bv32 == w32 as bv32;
  expect x32 * 3 == m32;
  expect x32 as bv32 >> s32 as bv32 == s32 as bv32;
  expect x32 as bv32 << o32 as bv32 == t32 as bv32;
  print "operators(u32) ";
}

method TestI32() {
  var o32: int32 := 1 as int32;
  var s32: int32 := 2 as int32;
  var w32: int32 := 5 as int32;
  var x32: int32 := 8 as int32;
  var y32: int32 := 13 as int32;
  var z32: int32 := 21 as int32;
  var m32: int32 := 24 as int32;
  var t32: int32 := 16 as int32;
  expect x32 + y32 == z32;
  expect x32 - y32 == -w32;
  expect x32 * 3 == m32;
  print "operators(i32) ";
}
method TestU64() {
  var o64: uint64 := 1 as uint64;
  var s64: uint64 := 2 as uint64;
  var w64: uint64 := 5 as uint64;
  var x64: uint64 := 8 as uint64;
  var y64: uint64 := 13 as uint64;
  var z64: uint64 := 21 as uint64;
  var m64: uint64 := 24 as uint64;
  var t64: uint64 := 16 as uint64;
  expect x64 + y64 == z64;
  expect y64 - x64 == w64;
  expect x64 as bv64 & y64 as bv64 == x64 as bv64;
  expect x64 as bv64 | y64 as bv64 == y64 as bv64;
  expect x64 as bv64 ^ y64 as bv64 == w64 as bv64;
  expect x64 * 3 == m64;
  expect x64 as bv64 >> s64 as bv64 == s64 as bv64;
  expect x64 as bv64 << o64 as bv64 == t64 as bv64;
  print "operators(u64) ";
}
method TestI64() {
  var o64: int64 := 1 as int64;
  var s64: int64 := 2 as int64;
  var w64: int64 := 5 as int64;
  var x64: int64 := 8 as int64;
  var y64: int64 := 13 as int64;
  var z64: int64 := 21 as int64;
  var m64: int64 := 24 as int64;
  var t64: int64 := 16 as int64;
  expect x64 + y64 == z64;
  expect x64 - y64 == -w64;
  expect x64 * 3 == m64;
  print "operators(i64) ";
}
method TestU128() {
  var o128: uint128 := 1 as uint128;
  var s128: uint128 := 2 as uint128;
  var w128: uint128 := 5 as uint128;
  var x128: uint128 := 8 as uint128;
  var y128: uint128 := 13 as uint128;
  var z128: uint128 := 21 as uint128;
  var m128: uint128 := 24 as uint128;
  var t128: uint128 := 16 as uint128;
  expect x128 + y128 == z128;
  expect y128 - x128 == w128;
  expect x128 as bv128 & y128 as bv128 == x128 as bv128;
  expect x128 as bv128 | y128 as bv128 == y128 as bv128;
  expect x128 as bv128 ^ y128 as bv128 == w128 as bv128;
  expect x128 * 3 == m128;
  expect x128 as bv128 >> s128 as bv128 == s128 as bv128;
  expect x128 as bv128 << o128 as bv128 == t128 as bv128;
  print "operators(u128)\n";
}

method TestI128() {
  var o128: int128 := 1 as int128;
  var s128: int128 := 2 as int128;
  var w128: int128 := 5 as int128;
  var x128: int128 := 8 as int128;
  var y128: int128 := 13 as int128;
  var z128: int128 := 21 as int128;
  var m128: int128 := 24 as int128;
  var t128: int128 := 16 as int128;
  expect x128 + y128 == z128;
  expect x128 - y128 == -w128;
  expect x128 * 3 == m128;
  print "operators(i128)\n";
}
method {:resource_limit "1e6"}  Main() {
  var t := true;
  var f := false;
  expect ((t && f) || f) ==> f;
  print "&& || ==> ";
  expect t && f <==> f && t;
  print "<==> ";

  expect 2 <= 3;
  expect 2 < 3;
  expect 3 >= 2;
  expect 3 > 2;
  expect 3 != 2;
  expect 2 == 2;
  print "<= < >= > != ==\n";

  expect 2 + 2 == 4;
  expect 2 * 2 == 4;
  expect 2 - 2 == 0;
  expect -1 / 2 == -1;
  expect 5 % 2 == 1;
  print "+ * - / %\n";
  TestU8();
  TestU16();
  TestU32();
  TestU64();
  TestU128();
  TestI8();
  TestI16();
  TestI32();
  TestI64();
  TestI128();
  
  var a := 'a';
  var z := 'z';
  expect a < z;
  expect z > a;
  expect a <= a;
  expect a >= a;
  expect a != z;
  expect a == a;
  expect !(a < a);
  expect !(z < a);
  expect !(z <= a);
  expect !(a >= z);
  print "char comparison\n";
  
  var m := map[1 := 2];
  expect 1 in m;
  expect 2 !in m;
  expect m[1] == 2;
  print "map contains acccess ";
  var m2 := m[2 := 4] - {1};
  expect 1 !in m2;
  expect 2 in m2;
  print "update union diff ";
  var m3 := map k | 2 <= k < 4 :: k := 2*k;
  expect m3 == map[3 := 6, 2 := 4];
  expect |m3| == 2;
  print "comprehension equality cardinality ";
  
  expect m3.Keys == {2, 3};
  expect m3.Values == {4, 6};
  expect m3.Items == {(2, 4), (3, 6)};
  print ".Keys .Values .Items\n";

  var st := {1};
  expect 1 in st;
  expect 2 !in st;
  print "set contains ";
  var t2 := st + {2} - {1};
  expect 1 !in t2;
  expect 2 in t2;
  print "union diff ";
  var t3 := set k | 2 <= k < 4 :: 2*k;
  expect t3 == {6, 4};
  expect |t3| == 2;
  expect {4, 6} <= t3;
  expect {4} < t3;
  expect t3 >= {4, 6};
  expect t3 > {6};
  print "comprehension equality cardinality ";
  expect t2 != t3;
  expect t2 * t3 == {};
  expect t2 !! t3;
  print "inequality and intersection\n";
  
  var s1 := seq(2, i => 1 + i);
  var s2 := s1 + [3];
  expect s1 <= s2;
  expect s1 < s2;
  expect s1 != s2;
  expect !(s2 <= s1);
  expect !(s2 < s1);
  expect s2 != s1;
  expect !(s1 == s2);
  print "sequence prefix ";
  var s3 := if |s2| == 3 then s2[2 := 4] else s2;
  expect s3[1] == 2;
  expect s3 == [1, 2, 4];
  expect |s3| == 3;
  print "sequence update cardinality ";

  var s4 := if |s3| >= 3 then s3[1..3] else s3;
  expect s4 == [2, 4];
  print "sequence slice\n";

  var h := multiset{1, 1, 2};
  var k := multiset([1, 2]);
  expect k < h;
  expect k <= h;
  expect h > k;
  expect h >= k;
  print "multiset comparison ";
  expect k + h == multiset{1, 1, 1, 2, 2};
  print "union equality ";
  expect 1 in h;
  expect h[1] == 2;
  expect |h| == 3;
  print "access and cardinality\n";
  
  var seq1: seq<int> := [1, 2, 3, 4];
  var seq2: int := seq1[0];
  var seq3: seq<int> := seq1[1..4];
  var seq4: seq<int> := seq3 + [seq2];
  expect seq4[0] == 2;
  expect seq4[3] == 1;
  expect seq4[0..3] == seq3;
  print "Sequence index slice comparison";
}
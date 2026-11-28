// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

newtype i8 = x: int | -0x80 <= x < 0x80
newtype i16 = x: int | -0x8000 <= x < 0x8000
newtype i32 = x: int | -0x80000000 <= x < 0x80000000
newtype i64 = x: int | -0x8000000000000000 <= x < 0x8000000000000000

// % with the minimum value as dividend
method Main() {
  var m8: i8 := -0x80;
  print m8 % -1, " ", m8 % 2, " ", m8 % 3, " ", m8 % -7, "\n";
  var m16: i16 := -0x8000;
  print m16 % -1, " ", m16 % 2, " ", m16 % 3, " ", m16 % -7, "\n";
  var m32: i32 := -0x80000000;
  print m32 % -1, " ", m32 % 2, " ", m32 % 3, " ", m32 % -7, "\n";
  var m64: i64 := -0x8000000000000000;
  print m64 % -1, " ", m64 % 2, " ", m64 % 3, " ", m64 % -7, "\n";
}

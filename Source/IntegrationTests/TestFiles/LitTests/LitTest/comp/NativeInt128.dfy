// NONUNIFORM: C#-specific native Int128 and UInt128 support.
// RUN: %run --no-verify --target cs "%s"
// RUN: %run --no-verify --target cs --include-runtime:false "%s"
// RUN: %translate cs %trargs --output=%t.cs "%s"
// RUN: %OutputCheck --file-to-check "%t.cs" "%s"
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK: internal static readonly Dafny\.TypeDescriptor<System\.Int128> INT128 = new Dafny\.TypeDescriptor<System\.Int128>\(0\);
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK: internal static readonly Dafny\.TypeDescriptor<System\.UInt128> UINT128 = new Dafny\.TypeDescriptor<System\.UInt128>\(0\);
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK: public static System\.Int128 SignedIdentity\(System\.Int128 @value\)
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK: public static System\.UInt128 UnsignedIdentity\(System\.UInt128 @value\)
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK: DefaultValue<System\.Int128>\(int128\._TypeDescriptor\(\)\)
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK: DefaultValue<System\.UInt128>\(uint128\._TypeDescriptor\(\)\)
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK-NOT: DefaultValue<System\.UInt128>\(new Dafny\.TypeDescriptor<System\.UInt128>
// CHECK: DefaultValue<System\.UInt128>\(global::FuncExtensions\.UINT128\)
// CHECK-NOT: DefaultValue<System\.UInt128>\(new Dafny\.TypeDescriptor<System\.UInt128>
// CHECK: DefaultValue<System\.UInt128>\(global::FuncExtensions\.UINT128\)
// CHECK-NOT: DefaultValue<System\.UInt128>\(new Dafny\.TypeDescriptor<System\.UInt128>
// CHECK: DefaultValue<System\.UInt128>\(global::FuncExtensions\.UINT128\)
// CHECK-NOT: DefaultValue<System\.UInt128>\(new Dafny\.TypeDescriptor<System\.UInt128>
// CHECK: DefaultValue<System\.UInt128>\(global::FuncExtensions\.UINT128\)
// CHECK-NOT: DefaultValue<System\.UInt128>\(new Dafny\.TypeDescriptor<System\.UInt128>
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK: private static readonly Dafny\.TypeDescriptor<System\.Int128> _TYPE = new Dafny\.TypeDescriptor<System\.Int128>
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)
// CHECK: private static readonly Dafny\.TypeDescriptor<System\.UInt128> _TYPE = new Dafny\.TypeDescriptor<System\.UInt128>
// CHECK-NOT: System\.(Int128|UInt128)\.Parse
// CHECK-NOT: Dafny\.Helpers\.(INT128|UINT128)

module DafnyInt128Helpers {
  method Touch() {
  }
}

newtype {:nativeType "doublelong"} int128 = x: int |
  -0x8000_0000_0000_0000_0000_0000_0000_0000 <= x <
   0x8000_0000_0000_0000_0000_0000_0000_0000

newtype {:nativeType "udoublelong"} uint128 = x: int |
  0 <= x < 0x1_0000_0000_0000_0000_0000_0000_0000_0000

function SignedIdentity(value: int128): int128 {
  value
}

function UnsignedIdentity(value: uint128): uint128 {
  value
}

method DefaultValue<T(0)>() returns (value: T) {
  value := *;
}

method CheckBoundsAndConversions() {
  var signedZero: int128 := 0;
  var signedOne: int128 := 1;
  var signedHot: int128 := 1_000_000_000_000_000_000;
  var signedMin: int128 := -0x8000_0000_0000_0000_0000_0000_0000_0000;
  var signedMax: int128 :=  0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
  var unsignedZero: uint128 := 0;
  var unsignedOne: uint128 := 1;
  var unsignedHot: uint128 := 1_000_000_000_000_000_000;
  var unsignedMax: uint128 := 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
  var signedAboveUlong: int128 := 0x1_0000_0000_0000_002a;
  var aboveUlong: uint128 := 0x1_0000_0000_0000_002a;
  var directSignedCast: int128 :=
    0x1_0000_0000_0000_0042 as int128;
  var directUnsignedCast: uint128 :=
    0x1_0000_0000_0000_0043 as uint128;

  expect signedZero == 0 && signedOne == 1;
  expect signedHot == 1_000_000_000_000_000_000;
  expect unsignedZero == 0 && unsignedOne == 1;
  expect unsignedHot == 1_000_000_000_000_000_000;
  expect SignedIdentity(signedMin) as int ==
    -0x8000_0000_0000_0000_0000_0000_0000_0000;
  expect SignedIdentity(signedMax) as int ==
     0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
  expect UnsignedIdentity(unsignedMax) as int ==
    0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
  expect aboveUlong as int == 0x1_0000_0000_0000_002a;
  expect directSignedCast as int == 0x1_0000_0000_0000_0042;
  expect directUnsignedCast as int == 0x1_0000_0000_0000_0043;

  var signedMath: int := -0x1_0000_0000_0000_002a;
  var unsignedMath: int := 0x1_0000_0000_0000_002a;
  expect (signedMath as int128) as int == signedMath;
  expect (unsignedMath as uint128) as int == unsignedMath;

  var signedReal: real := signedAboveUlong as real;
  var unsignedReal: real := aboveUlong as real;
  expect signedReal as int128 == signedAboveUlong;
  expect unsignedReal as uint128 == aboveUlong;

  var signedOrdinal: ORDINAL := signedAboveUlong as ORDINAL;
  var unsignedOrdinal: ORDINAL := aboveUlong as ORDINAL;
  var signedFromOrdinal: int128 := signedOrdinal as int128;
  var unsignedFromOrdinal: uint128 := unsignedOrdinal as uint128;
  expect signedFromOrdinal == signedAboveUlong;
  expect unsignedFromOrdinal == aboveUlong;

  var signedDefault: int128 := DefaultValue();
  var unsignedDefault: uint128 := DefaultValue();
  var bitvector65Default: bv65 := DefaultValue();
  var bitvector100Default: bv100 := DefaultValue();
  var bitvector127Default: bv127 := DefaultValue();
  var bitvector128Default: bv128 := DefaultValue();
  expect signedDefault == 0;
  expect unsignedDefault == 0;
  expect bitvector65Default == 0;
  expect bitvector100Default == 0;
  expect bitvector127Default == 0;
  expect bitvector128Default == 0;
}

method CheckSignedOperations() {
  var positive: int128 :=  0x1_0000_0000_0000_0005;
  var negative: int128 := -0x1_0000_0000_0000_0003;
  expect negative < 0 < positive;
  expect positive != negative;
  expect negative <= positive;
  expect positive > negative;
  expect positive >= positive;
  expect positive + negative == 2;
  expect positive - negative == 0x2_0000_0000_0000_0008;
  expect positive * (-3) == -0x3_0000_0000_0000_000f;

  var signedBits: bv128 := positive as bv128;
  expect signedBits & (0xffff_ffff_ffff_ffff as bv128) == 5;
  expect signedBits | (0xf0 as bv128) ==
    0x1_0000_0000_0000_00f5;
  expect signedBits ^ (0xff as bv128) ==
    0x1_0000_0000_0000_00fa;
}

method CheckUnsignedOperations() {
  var left: uint128 :=  0x1_0000_0000_0000_0005;
  var right: uint128 := 0x1_0000_0000_0000_0003;
  expect right < left;
  expect left != right;
  expect right <= left;
  expect left > right;
  expect left >= left;
  expect left + right == 0x2_0000_0000_0000_0008;
  expect left - right == 2;
  expect left * 3 == 0x3_0000_0000_0000_000f;

  expect (left as bv128) & (right as bv128) ==
    0x1_0000_0000_0000_0001;
  expect (left as bv128) | (right as bv128) ==
    0x1_0000_0000_0000_0007;
  expect (left as bv128) ^ (right as bv128) == 6;
}

method CheckSignedDivision(
  dividend: int128,
  divisor: int128,
  quotient: int128,
  remainder: int128
)
  requires divisor != 0
  requires -0x8000_0000_0000_0000_0000_0000_0000_0000 <=
    (dividend as int) / (divisor as int) <
    0x8000_0000_0000_0000_0000_0000_0000_0000
{
  expect dividend / divisor == quotient;
  expect dividend % divisor == remainder;
}

method CheckDivision() {
  CheckSignedDivision( 7,  3,  2, 1);
  CheckSignedDivision( 7, -3, -2, 1);
  CheckSignedDivision(-7,  3, -3, 2);
  CheckSignedDivision(-7, -3,  3, 2);
  CheckSignedDivision( 0,  3,  0, 0);
  CheckSignedDivision( 0, -3,  0, 0);

  var signedMin: int128 :=
    -0x8000_0000_0000_0000_0000_0000_0000_0000;
  CheckSignedDivision(7, signedMin, 0, 7);
  CheckSignedDivision(
    -7,
    signedMin,
    1,
    0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_fff9
  );
  CheckSignedDivision(signedMin, signedMin, 1, 0);
  expect signedMin / 1 == signedMin;
  expect signedMin / 2 ==
    -0x4000_0000_0000_0000_0000_0000_0000_0000;
  expect signedMin / -2 ==
     0x4000_0000_0000_0000_0000_0000_0000_0000;
  expect signedMin % -1 == 0;
  expect signedMin % 2 == 0;

  var unsignedMax: uint128 :=
    0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
  expect unsignedMax / 2 ==
    0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
  expect unsignedMax % 2 == 1;

  var aboveUlong: uint128 := 0x1_0000_0000_0000_0003;
  expect aboveUlong / 2 == 0x8000_0000_0000_0001;
  expect aboveUlong % 2 == 1;
}

method CheckBitvectorMasksAndWrapping() {
  var mask65: bv65 := -1;
  var mask100: bv100 := -1;
  var mask127: bv127 := -1;
  var mask128: bv128 := -1;

  expect mask65 as int == 0x1_ffff_ffff_ffff_ffff;
  expect mask100 as int == 0xf_ffff_ffff_ffff_ffff_ffff_ffff;
  expect mask127 as int == 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;
  expect mask128 as int == 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;

  expect mask65 + 1 == 0;
  expect mask100 + 1 == 0;
  expect mask127 + 1 == 0;
  expect mask128 + 1 == 0;

  expect (0 as bv65) - 1 == mask65;
  expect (0 as bv100) - 1 == mask100;
  expect (0 as bv127) - 1 == mask127;
  expect (0 as bv128) - 1 == mask128;

  expect mask65 * 2 == 0x1_ffff_ffff_ffff_fffe;
  expect mask100 * 2 == 0xf_ffff_ffff_ffff_ffff_ffff_fffe;
  expect mask127 * 2 == 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_fffe;
  expect mask128 * 2 == 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_fffe;

  expect !mask128 == 0; // Bitvector complement, emitted as C# ~.
}

method CheckShifts() {
  var one: bv128 := 1;
  var allBits: bv128 := -1;

  expect one << 0 == 1;
  expect one << 63 == 0x8000_0000_0000_0000;
  expect one << 64 == 0x1_0000_0000_0000_0000;
  expect one << 127 == 0x8000_0000_0000_0000_0000_0000_0000_0000;
  expect one << 128 == 0;

  expect allBits >> 0 == allBits;
  expect allBits >> 63 == 0x1_ffff_ffff_ffff_ffff;
  expect allBits >> 64 == 0xffff_ffff_ffff_ffff;
  expect allBits >> 127 == 1;
  expect allBits >> 128 == 0;
}

method CheckArrays() {
  var signedSize: int128 := 3;
  var unsignedSize: uint128 := 3;
  var signedIndex: int128 := 1;
  var unsignedIndex: uint128 := 2;

  var signedSized := new int[signedSize];
  var unsignedSized := new int[unsignedSize];
  signedSized[signedIndex] := 11;
  unsignedSized[unsignedIndex] := 22;
  expect signedSized[signedIndex] == 11;
  expect unsignedSized[unsignedIndex] == 22;

  var signedLength: int128 := unsignedSized.Length as int128;
  var unsignedLength: uint128 := signedSized.Length as uint128;
  expect signedLength == signedSize;
  expect unsignedLength == unsignedSize;
}

method Main() {
  CheckBoundsAndConversions();
  CheckSignedOperations();
  CheckUnsignedOperations();
  CheckDivision();
  CheckBitvectorMasksAndWrapping();
  CheckShifts();
  CheckArrays();
}

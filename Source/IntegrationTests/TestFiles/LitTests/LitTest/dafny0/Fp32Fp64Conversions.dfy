// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// Tests for conversions between fp32, fp64, real, and int
//
// The 'as' operator requires exact representability (lossless conversion).

// ============================================================================
// POSITIVE TESTS - These should verify successfully
// ============================================================================

method TestFp32ToFp64() {
  var x32: fp32 := 1.5;
  var x64: fp64 := x32 as fp64;
  assert x64 == 1.5;
}

method TestFp64ToFp32Exact() {
  var x64: fp64 := 1.5;
  var x32: fp32 := x64 as fp32;
  assert x32 == 1.5;
}

method TestFp32ToReal() {
  var f32: fp32 := 1.5;
  var r: real := f32 as real;
  assert r == 1.5;
}

method TestFp32ToInt() {
  var f: fp32 := 3.0;
  var i: int := f as int;
  assert i == 3;
}

method TestFp64ToReal() {
  var f64: fp64 := 2.5;
  var r: real := f64 as real;
  assert r == 2.5;
}

method TestFp64ToInt() {
  var f: fp64 := 42.0;
  var i: int := f as int;
  assert i == 42;
}

method TestIntToFp32() {
  var f: fp32 := 42 as fp32;
}

method TestIntToFp64() {
  var f: fp64 := 42 as fp64;
}

method TestMixedArithmetic() {
  var a32: fp32 := 2.0;
  var b64: fp64 := 3.0;
  var sum64: fp64 := (a32 as fp64) + b64;
  assert sum64 == 5.0;
  var sum32: fp32 := a32 + (b64 as fp32);
  assert sum32 == 5.0;
}

// ============================================================================
// NEGATIVE TESTS - These should fail verification
// ============================================================================

// Should fail: fp64 value not exactly representable in fp32
method TestFp64ToFp32Lossy() {
  var f: fp32 := ~1.23456789012345 as fp64 as fp32;
}

// Should fail: infinity not convertible to real
method TestFp32InfinityToReal() {
  var inf: fp32 := fp32.PositiveInfinity;
  var r: real := inf as real;
}

// Should fail: infinity not convertible to real
method TestFp64InfinityToReal() {
  var inf: fp64 := fp64.PositiveInfinity;
  var r: real := inf as real;
}

// Should fail: not an exact integer
method TestFp32NonIntegerToInt() {
  var f: fp32 := 3.5;
  var i: int := f as int;
}

// Should fail: not an exact integer
method TestFp64NonIntegerToInt() {
  var f: fp64 := ~3.14;
  var i: int := f as int;
}

// Should fail: 0.1 not exactly representable in fp64
method TestInexactRealToFp64() {
  var f: fp64 := 0.1 as fp64;
}

// Should fail: 0.1 not exactly representable (caught at fp64 step)
method TestInexactRealToFp32ViaFp64() {
  var f: fp32 := 0.1 as fp64 as fp32;
}

// Should fail: integer too large for fp64 precision
method TestLargeIntToFp64() {
  var f: fp64 := 9007199254740993 as fp64;  // 2^53 + 1
}

// Should fail: integer too large for fp32 precision
method TestLargeIntToFp32() {
  var f: fp32 := 16777217 as fp32;  // 2^24 + 1
}

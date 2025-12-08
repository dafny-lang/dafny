// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

method TestTildeOnExactFp32Literals() {
  // ERROR: Using ~ on exactly representable values is forbidden
  // The ~ prefix is only for acknowledging inexact representation

  var bad1: fp32 := ~1.0;   // Error: ~ not allowed; 1.0 is exactly representable in fp32
  var bad2: fp32 := ~0.5;   // Error: ~ not allowed; 0.5 is exactly representable in fp32
  var bad3: fp32 := ~0.25;  // Error: ~ not allowed; 0.25 is exactly representable in fp32
  var bad4: fp32 := ~2.0;   // Error: ~ not allowed; 2.0 is exactly representable in fp32
  var bad5: fp32 := ~4.0;   // Error: ~ not allowed; 4.0 is exactly representable in fp32
  var bad6: fp32 := ~0.125; // Error: ~ not allowed; 0.125 is exactly representable in fp32
}

method TestTildeOnExactFp64Literals() {
  // ERROR: Using ~ on exactly representable values is forbidden
  // The ~ prefix is only for acknowledging inexact representation

  var bad1: fp64 := ~1.0;   // Error: ~ not allowed; 1.0 is exactly representable in fp64
  var bad2: fp64 := ~0.5;   // Error: ~ not allowed; 0.5 is exactly representable in fp64
  var bad3: fp64 := ~0.25;  // Error: ~ not allowed; 0.25 is exactly representable in fp64
  var bad4: fp64 := ~2.0;   // Error: ~ not allowed; 2.0 is exactly representable in fp64
  var bad5: fp64 := ~4.0;   // Error: ~ not allowed; 4.0 is exactly representable in fp64
  var bad6: fp64 := ~0.125; // Error: ~ not allowed; 0.125 is exactly representable in fp64
}

// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// An instance const's initializer sees the consts that the constructor assigns.

newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000

class P {
  const a: i32
  const b: i32 := if a < 100 then a + 1 else a
  constructor(a: i32) { this.a := a; }
}

method Main() {
  var p := new P(5);
  print p.b, "\n";
}

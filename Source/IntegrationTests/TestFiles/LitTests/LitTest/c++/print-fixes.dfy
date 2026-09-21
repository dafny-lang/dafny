// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation --allow-deprecation --unicode-char false

// Regression test for C++ backend printing fixes. The minimal `c++` target rejects
// unbounded `int`, so everything here uses native newtypes. Runs on every backend,
// so it also pins that C++ now matches the others.
//   - printing a whole datatype value: `Typename.Ctor(fields)`
//   - set / map / tuple print format
//   - map-literal last-value-wins on a duplicate key
//   - 8-bit newtype printed as a number, not a raw byte

newtype u8 = i: int | 0 <= i < 256
newtype u32 = i: int | 0 <= i < 0x100000000

datatype Color = Red | Blue(x: u32, ok: bool)

method Main() {
  // Printing a whole datatype value.
  print Red, "\n";
  print Blue(3, true), "\n";

  // Set and map print format (native-typed elements/keys).
  var s: set<u32> := {1};
  print s, "\n";
  var m: map<u32, u32> := map[1 := 10];
  print m, "\n";

  // Tuple print format.
  print (1 as u32, true), "\n";

  // Map literal with a duplicate key: the LAST value wins.
  var dup: map<u32, u32> := map[0 := 1, 0 := 2];
  print dup[0], "\n";

  // 8-bit newtype prints as a number, not a raw byte.
  var b: u8 := 255;
  print b, "\n";
}

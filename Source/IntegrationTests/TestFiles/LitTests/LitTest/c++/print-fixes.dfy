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

  // Record, recursive, and generic datatypes.
  print Rec(1, false), "\n";
  print Link(1, Link(2, End)), "\n";
  var j: Maybe<u32> := Just(7);
  print j, "\n";

  // 8-bit and bool values inside collections and tuples.
  var c: u8 := 65;
  print [c], " ", {c}, " ", (c, true), " ", [true, false], "\n";
}

datatype Rec = Rec(a: u32, b: bool)
datatype Chain = End | Link(h: u32, t: Chain)
datatype Maybe<T> = Nothing | Just(v: T)

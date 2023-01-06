// RUN: %exits-with 2 %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// && and || have the same binding power and do not associate with each other.
// The same goes for ==> and <==, and for &, |, and ^.
// The tests below check that these ambiguities result in understandable error message.

method M0() returns (A: bool, B: bool)
  ensures A && B || A // error: and-or ambiguity

method M1() returns (A: bool, B: bool)
  ensures A || B && A // error: and-or ambiguity

method M2() returns (A: bool, B: bool)
  ensures && B || A // error: and-or ambiguity

method M3() returns (A: bool, B: bool)
  ensures || B && A // error: and-or ambiguity

method M4() returns (A: bool, B: bool)
  ensures && A && B || A // error: and-or ambiguity

method M5() returns (A: bool, B: bool)
  ensures || A || B && A // error: and-or ambiguity

// ---

method N0() returns (A: bool, B: bool, C: bool)
  ensures A ==> B <== A // error: implication/explication ambiguity

method N1() returns (A: bool, B: bool, C: bool)
  ensures A ==> B ==> C <== A // error: implication/explication ambiguity

method N2() returns (A: bool, B: bool, C: bool)
  ensures A <== B ==> A // error: implication/explication ambiguity

method N3() returns (A: bool, B: bool, C: bool)
  ensures A <== B <== C ==> A // error: implication/explication ambiguity

// ---

method P0() returns (a: bv8, b: bv8)
  ensures a & b | a // error: bitwise-op ambiguity

method P1() returns (a: bv8, b: bv8)
  ensures a & b ^ a // error: bitwise-op ambiguity

method P2() returns (a: bv8, b: bv8)
  ensures a | b ^ a // error: bitwise-op ambiguity

method P3() returns (a: bv8, b: bv8)
  ensures a | b & a // error: bitwise-op ambiguity

method P4() returns (a: bv8, b: bv8)
  ensures a ^ b & a // error: bitwise-op ambiguity

method P5() returns (a: bv8, b: bv8)
  ensures a ^ b | a // error: bitwise-op ambiguity

// ---

method SwanSong() returns (A: bool, B: bool, C: bool)
  ensures A || B && C  // error: and-or ambiguity (this also gives an EOF error message for the C)

method PostSwanSong() returns (A: bool, B: bool, C: bool)
  ensures A || B && C  // since the parser already expected an EOF above, it doesn't even get here

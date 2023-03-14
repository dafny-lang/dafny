// RUN: %baredafny run --target java "%s" > "%t"
// RUN: %baredafny run --target cs "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint8 = x : int | 0 <= x < 256

method Main() {
  var y := 0x80 as bv8;
  var x := (y >> 4) as uint8;
  print y, " >> 4 == ", x, "\n";
  assert x != 248; // What Java obtained before when computing "y >>> 4"
  assert x == 0x8;
  if x == 248 {
    var x := 1/0; // Should not be executed
  }

  var z: bv32 := 12;
  assert (z >> 31) == 0;
  print "12 >> 31 == ", z >> 31, ", ";
  assert (z >> 32) == 0;
  print "12 >> 32 == ", z >> 32, "\n";
  print "All right";
}
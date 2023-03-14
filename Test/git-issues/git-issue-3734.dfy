// RUN: %baredafny run --target java "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint8 = x : int | 0 <= x < 256

method Main() {
  var y := 0x80 as bv8;
  var x := (y >> 4) as uint8;
  print "Java believes ", y, " >> 4 == ", x, "\n";
  assert x != 248; // What Java obtained before when computing "y >>> 4"
  assert x == 0x8;
  if x == 248 {
    var x := 1/0; // Should not be executed
  }
  print "All right";
}
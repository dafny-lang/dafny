// RUN: %baredafny verify "%s"
 // RUN: %testDafnyForEachCompiler "%s"

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
  
  Right();
  Left();
}

method Right() {
  var m: bv0 := 0;
  print m >> 0, "\n"; // 0
  var n: bv1 := 1;
  print n >> 0, " ", n >> 1, "\n"; // 1 0

  var a: bv7 := 12;
  print a >> 0, " ", a >> 1, " ", a >> 6, " ", a >> 7, " "; // 12 6 0 0
  a := -1;
  print a >> 0, " ", a >> 6, "\n"; // 127 1

  var b: bv8 := 12;
  print b >> 0, " ", b >> 1, " ", b >> 7, " ", b >> 8, " "; // 12 6 0 0
  b := -1;
  print b >> 0, " ", b >> 7, "\n"; // 255 1

  var r: bv15 := 12;
  print r >> 0, " ", r >> 1, " ", r >> 14, " ", r >> 15, " "; // 12 6 0 0
  r := -1;
  print r >> 0, " ", r >> 14, "\n"; // 32767 1

  var s: bv16 := 12;
  print s >> 0, " ", s >> 1, " ", s >> 15, " ", s >> 16, " "; // 12 6 0 0
  s := -1;
  print s >> 0, " ", s >> 15, "\n"; // 65535 1

  var w: bv31 := 12;
  print w >> 0, " ", w >> 1, " ", w >> 30, " ", w >> 31, " "; // 12 6 0 0
  w := -1;
  print w >> 0, " ", w >> 30, "\n"; // 0x7fff_ffff 1

  var x: bv32 := 12;
  print x >> 0, " ", x >> 1, " ", x >> 31, " ", x >> 32, " "; // 12 6 0 0
  x := -1;
  print x >> 0, " ", x >> 31, "\n"; // 0xffff_ffff 1

  var y: bv63 := 12;
  print y >> 0, " ", y >> 1, " ", y >> 62, " ", y >> 62, " "; // 12 6 0 0
  y := -1;
  print y >> 0, " ", y >> 62, "\n"; // 0x7fff_ffff_ffff_ffff 1

  var z: bv64 := 12;
  print z >> 0, " ", z >> 1, " ", z >> 63, " ", z >> 64, " "; // 12 6 0 0
  z := -1;
  print z >> 0, " ", z >> 63, "\n"; // 0xffff_ffff_ffff_ffff 1

  var u: bv100 := 12;
  print u >> 0, " ", u >> 1, " ", u >> 99, " ", u >> 100, " "; // 12 6 0 0
  u := -1;
  print u >> 0, " ", u >> 99, "\n"; // 0xf_ffff_ffff_ffff_ffff_ffff_ffff 1
}

method Left() {
  var m: bv0 := 0;
  print m << 0, "\n"; // 0
  var n: bv1 := 1;
  print n << 0, " ", n << 1, "\n"; // 1 0

  var a: bv7 := 12;
  print a << 0, " ", a << 1, " ", a << 6, " ", a << 7, " "; // 12 24 0 0
  a := -1;
  print a << 0, " ", a << 6, "\n"; // 127 64

  var b: bv8 := 12;
  print b << 0, " ", b << 1, " ", b << 7, " ", b << 8, " "; // 12 24 0 0
  b := -1;
  print b << 0, " ", b << 7, "\n"; // 255 128

  var r: bv15 := 12;
  print r << 0, " ", r << 1, " ", r << 14, " ", r << 15, " "; // 12 24 0 0
  r := -1;
  print r << 0, " ", r << 14, "\n"; // 32767 16384

  var s: bv16 := 12;
  print s << 0, " ", s << 1, " ", s << 15, " ", s << 16, " "; // 12 24 0 0
  s := -1;
  print s << 0, " ", s << 15, "\n"; // 65535 32768

  var w: bv31 := 12;
  print w << 0, " ", w << 1, " ", w << 30, " ", w << 31, " "; // 12 24 0 0
  w := -1;
  print w << 0, " ", w << 30, "\n"; // 0x7fff_ffff 0x4000_0000

  var x: bv32 := 12;
  print x << 0, " ", x << 1, " ", x << 31, " ", x << 32, " "; // 12 24 0 0
  x := -1;
  print x << 0, " ", x << 31, "\n"; // 0xffff_ffff 0x8000_0000

  var y: bv63 := 12;
  print y << 0, " ", y << 1, " ", y << 62, " ", y << 62, " "; // 12 24 0 0
  y := -1;
  print y << 0, " ", y << 62, "\n"; // 0x7fff_ffff_ffff_ffff 0x4000_0000_0000_0000

  var z: bv64 := 12;
  print z << 0, " ", z << 1, " ", z << 63, " ", z << 64, " "; // 12 24 0 0
  z := -1;
  print z << 0, " ", z << 63, "\n"; // 0xffff_ffff_ffff_ffff 0x8000_0000_0000_0000

  var u: bv100 := 12;
  print u << 0, " ", u << 1, " ", u << 99, " ", u << 100, " "; // 12 24 0 0
  u := -1;
  print u << 0, " ", u << 99, "\n"; // 0xf_ffff_ffff_ffff_ffff_ffff_ffff 0x8_0000_0000_0000_0000_0000_0000 
}
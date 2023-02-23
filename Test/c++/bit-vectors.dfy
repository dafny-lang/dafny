// RUN: %dafny /compile:3 /spillTargetCode:2 /compileTarget:cpp "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype uint64 = i:int | 0 <= i < 0x10000000000000000

function bit(i: uint64) : bv64
  requires i < 64
  {
    1 as bv64 << i
  }

method BasicOps(b0:bv64, b1:bv64) {
  var r0:bv64 := b0 & b1;
  var r1:bv64 := b0 | b1;
  var r2:bv64 := b0 ^ b1;
  var r3:bv64 := b0 ^ 0xffff_ffff_ffff_ffff;
  var r4:bv64 := b0 << 4;

  var r5 := r0 & r1 & r2 & r3 & r4;
  print r5;

}

lemma {:axiom} as_int_as_bv64(a: bv64)
  ensures (a as int) as bv64 == a
  ensures (a as int) < 0x10000000000000000

method Casts(u0:uint64)
{
  var r0:bv64 := u0 as bv64 << 1;
  as_int_as_bv64(u0 as bv64 << 1);
  var r1:uint64 := (u0 as bv64 << 1) as uint64;
  print r0, r1;
}

method Main() {
  BasicOps(72, 15);
  Casts(42);
  var b := bit(10);
  print b, "\n";
}

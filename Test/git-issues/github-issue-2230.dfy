// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
lemma MergeLShift(v: bv128, i: nat, j: nat)
  requires i <= 128 && j <= 128 && i + j <= 128
  ensures v << i << j == v << i + j

method M2(i: nat)
  requires i <= 64
{
  ghost var half: bv128 := 0xffff_ffff_ffff_ffff;
  MergeLShift(half, 64, 64 - i);
  assert half << 64 - i << 64 == half << (128 - i);
}

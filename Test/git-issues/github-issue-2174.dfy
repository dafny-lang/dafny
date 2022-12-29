// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
// Taken from https://github.com/dafny-lang/dafny/issues/2174
lemma lm(val: bv16, idx: nat)
  requires 0 <= idx <= 16 - 8
  requires 0 <= val < (1 << 8)
  ensures val as bv32 << idx == (val << idx) as bv32 {}

// This example is from issue #2174 but is not yet fast. It's a somewhat
// convoluted example meant to help diagnose the problem, though, and
// essentially works around the fix, so it's probably okay that it's
// still slow.
/*
lemma lmnat(val: bv16, idx: nat)
  requires 0 <= idx <= 8
  requires 0 <= val < (1 << 8)
  ensures var idx32 := idx as bv32;
          val as bv32 << idx32 == (val << idx32) as bv32
{}
*/

lemma lmbv(val: bv16, idx: bv32)
  requires 0 <= idx <= 8
  requires 0 <= val < (1 << 8)
  ensures val as bv32 << idx == (val << idx) as bv32
{}

lemma lmnat'(val: bv16, idx: nat)
  requires 0 <= idx <= 8
  requires 0 <= (idx as bv32) <= 8
  requires 0 <= val < (1 << 8)
  ensures var idx32 := idx as bv32;
          val as bv32 << idx32 == (val << idx32) as bv32
{}

const Half: bv128 := 0xffff_ffff_ffff_ffff;
const Ones: bv128 := 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff;

method M(i: nat) {
  if i == 64 {
    assert Ones << i == Ones << 64;
  }
}

lemma CommLShiftUpCast(v: bv64, idx: nat)
  requires idx <= 64
  requires v as bv128 << idx < 1 << 64
  ensures (v << idx) as bv128 == v as bv128 << idx
{}

// This only succeeds with `requires idx < 64`, differing from the
// example in issue #2174.
lemma MaskedCommLShiftUpCast(v: bv64, idx: nat)
  requires idx < 64
  ensures (v as bv128 << idx) & Half == (v << idx) as bv128
{}

lemma PushUpCastIntoLShift(v: bv64, idx: nat)
  requires idx <= 64
  requires v as bv128 << idx < 1 << 64
  ensures (v as bv128 << idx) as bv64 == v as bv64 << idx;
{}

lemma UpCastLShiftMasking(v: bv64, idx: nat)
  requires 0 <= idx <= 64
  ensures v as bv128 << 64 == (v as bv128 << 64) & (Ones << idx);
{}

lemma UpCastRShiftMasking(v: bv64, idx: nat)
  requires 0 <= idx <= 64
  ensures v as bv128 == (v as bv128) & (Ones >> idx);
{}

lemma RightMask(v: bv64, i: nat)
  requires 64 <= i <= 128
  ensures v as bv128 & (Ones >> i) == (v & (0xffff_ffff_ffff_ffff >> i - 64)) as bv128
{}

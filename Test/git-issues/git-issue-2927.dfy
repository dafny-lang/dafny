// RUN: %exits-with 0 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "BoundedInts.dfy"

module {:options "-functionSyntax:4"} DafnyNaCl
{
  import opened BoundedInts

  // M2256 = 2**256
  const M2256 := 0x1_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000

  // P = 2**255 - 19
  const P := 0x8000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000_0000 - 19

  // Number of GF Digits. 15 digits of 16 bits each is 256 bits.
  const NGFD := 16
  const LM := 65536
  const LMM1 := 65535
  const R2256 := M2256 % P // 38 on a good day

  const MGFLC := (R2256 * 15) + 1

  const MGFLP := LMM1 * LMM1

  type Index_16 = x : nat | 0 <= x < NGFD

  type GF64_Any_Limb = i : int64 | -LM as int64 <= i <= (MGFLC * MGFLP) as int64
  type UGF64 = seq<GF64_Any_Limb>
  
  type GF64 = a : UGF64 | |a| == NGFD witness seq(NGFD, _ => 0)

  type Normal_GF64_OK      = a : GF64 | (forall i : Index_16 :: 0 <= a[i] <= LMM1 as GF64_Any_Limb) witness *
  type Normal_GF64_Crashes = a : GF64 | (forall i : Index_16 :: 0 <= a[i] <= LMM1 as GF64_Any_Limb) witness seq(NGFD, _ => 0)

}

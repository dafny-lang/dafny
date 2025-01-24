/*******************************************************************************
 *  Original: Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *  
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/* Every lemma comes in 2 forms: 'LemmaProperty' and 'LemmaPropertyAuto'. The
former takes arguments and may be more stable and less reliant on Z3
heuristics. The latter includes automation and its use requires less effort */

module {:disableNonlinearArithmetic} Std.Arithmetic.Power2 {
  import opened GeneralInternals
  import opened MulInternals
  import opened Power

  function Pow2(e: nat): nat
    ensures Pow2(e) > 0
  {
    LemmaPowPositive(2, e);
    Pow(2, e)
  }

  /* Pow2() is equivalent to Pow() with base 2. */
  lemma LemmaPow2(e: nat)
    ensures Pow2(e) == Pow(2, e)
  {

    if e != 0 {
      LemmaPow2(e - 1);
    }
  }

  lemma LemmaPow2Auto()
    ensures forall e: nat {:trigger Pow2(e)} :: Pow2(e) == Pow(2, e)
  {

    forall e: nat {:trigger Pow2(e)}
      ensures Pow2(e) == Pow(2, e)
    {
      LemmaPow2(e);
    }
  }

  /* (2^e - 1) / 2 = 2^(e - 1) - 1 */
  // keep
  lemma LemmaPow2MaskDiv2(e: nat)
    requires 0 < e
    ensures (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1
  {
    LemmaPow2Auto();
    LemmaPowAuto();
    var f := e => 0 < e ==> (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1;
    assert forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    LemmaMulInductionAuto(e, f);
  }

  lemma LemmaPow2MaskDiv2Auto()
    ensures forall e: nat {:trigger Pow2(e)} :: 0 < e ==>
                                                  (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1
  {
    forall e: nat {:trigger Pow2(e)} | 0 < e
      ensures (Pow2(e) - 1) / 2 == Pow2(e - 1) - 1
    {
      LemmaPow2MaskDiv2(e);
    }
  }

  lemma Lemma2To64()
    ensures Pow2(0) == 0x1
    ensures Pow2(1) == 0x2
    ensures Pow2(2) == 0x4
    ensures Pow2(3) == 0x8
    ensures Pow2(4) == 0x10
    ensures Pow2(5) == 0x20
    ensures Pow2(6) == 0x40
    ensures Pow2(7) == 0x80
    ensures Pow2(8) == 0x100
    ensures Pow2(9) == 0x200
    ensures Pow2(10) == 0x400
    ensures Pow2(11) == 0x800
    ensures Pow2(12) == 0x1000
    ensures Pow2(13) == 0x2000
    ensures Pow2(14) == 0x4000
    ensures Pow2(15) == 0x8000
    ensures Pow2(16) == 0x10000
    ensures Pow2(17) == 0x20000
    ensures Pow2(18) == 0x40000
    ensures Pow2(19) == 0x80000
    ensures Pow2(20) == 0x100000
    ensures Pow2(21) == 0x200000
    ensures Pow2(22) == 0x400000
    ensures Pow2(23) == 0x800000
    ensures Pow2(24) == 0x1000000
    ensures Pow2(25) == 0x2000000
    ensures Pow2(26) == 0x4000000
    ensures Pow2(27) == 0x8000000
    ensures Pow2(28) == 0x10000000
    ensures Pow2(29) == 0x20000000
    ensures Pow2(30) == 0x40000000
    ensures Pow2(31) == 0x80000000
    ensures Pow2(32) == 0x100000000
    ensures Pow2(64) == 0x10000000000000000
  {
  }

}

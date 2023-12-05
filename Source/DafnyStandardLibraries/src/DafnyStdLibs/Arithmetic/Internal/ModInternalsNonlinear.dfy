/*******************************************************************************
 *  Original: Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *  
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/**
Several lemmas in this module are bodyless and marked as axiom.
These lemmas could previously be proven with an empty body, but only if this file was verified by itself,
not with the rest of the standard library.
If we want to remove the {:axiom} annotation from these lemmas, 
we will have to investigate why they only verify under specific conditions.   
*/
module {:z3ArithmeticSolver 6} DafnyStdLibs.Arithmetic.ModInternalsNonlinear {

  /* WARNING: Think three times before adding to this file, as nonlinear
  verification is highly unstable! */

  /* the remainder of 0 divided by an integer is 0 */
  lemma LemmaModOfZeroIsZero(m:int)
    requires 0 < m
    ensures 0 % m == 0
  {
  }

  /* describes fundementals of the modulus operator */
  lemma LemmaFundamentalDivMod(x:int, d:int)
    requires d != 0
    ensures x == d * (x / d) + (x % d) {
  }


  /* the remained of 0 divided by any integer is always 0 */
  lemma Lemma0ModAnything()
    ensures forall m: int {:trigger 0 % m} :: m > 0 ==> 0 % m == 0 {
  }

  /* a natural number x divided by a larger natural number gives a remainder equal to x */
  lemma LemmaSmallMod(x:nat, m:nat)
    requires x < m
    requires 0 < m
    ensures x % m == x {
  }

  /* the range of the modulus of any integer will be [0, m) where m is the divisor */
  lemma LemmaModRange(x:int, m:int)
    requires m > 0
    ensures 0 <= x % m < m
  {
  }

}

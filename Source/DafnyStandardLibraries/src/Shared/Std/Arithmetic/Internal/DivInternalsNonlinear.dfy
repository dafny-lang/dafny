/*******************************************************************************
 *  Original: Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *  
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

module {:z3ArithmeticSolver 6} Std.Arithmetic.DivInternalsNonlinear {

  /* WARNING: Think three times before adding to this file, as nonlinear
  verification is highly unstable! */

  /* zero divided by an integer besides 0 is 0 */
  lemma LemmaDivOf0(d:int)
    requires d != 0
    ensures 0 / d == 0
  {
  }

  /* the quotient of an integer divided by itself is 1 */
  lemma LemmaDivBySelf(d:int)
    requires d != 0
    ensures d / d == 1
  {
  }

  /* dividing a smaller integer by a larger integer results in a quotient of 0  */
  lemma LemmaSmallDiv()
    ensures forall x, d {:trigger x / d} :: 0 <= x < d && d > 0 ==> x / d == 0 {
  }

  /* the quotient of dividing a positive real number (not 0) by a smaller positive real number
  will be greater than 1 */
  lemma LemmaRealDivGt(x:real, y:real)
    requires x > y
    requires y > 0.0
    ensures  x / y > 1 as real {
  }

}

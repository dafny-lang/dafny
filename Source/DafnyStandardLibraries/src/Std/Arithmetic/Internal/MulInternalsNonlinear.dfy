/*******************************************************************************
 *  Original: Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *  
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

module {:z3ArithmeticSolver 6} Std.Arithmetic.MulInternalsNonlinear {

  /* WARNING: Think three times before adding to this file, as nonlinear
  verification is highly unstable! */

  /* multiplying two positive integers will result in a positive integer */
  lemma LemmaMulStrictlyPositive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
  {}

  /* multiplying two nonzero integers will never result in 0 as the poduct */
  lemma LemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
  {}

  /* multiplication is associative */
  lemma LemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
  {}

  /* multiplication is distributive */
  lemma LemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  {}

  /* the product of two integers is greater than the value of each individual integer */
  lemma LemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
  {}

  /* multiplying by a positive integer preserves inequality */
  lemma LemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures  x * z < y * z
  {}

}

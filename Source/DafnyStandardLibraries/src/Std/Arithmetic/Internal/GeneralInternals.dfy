/*******************************************************************************
 *  Original: Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *  
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

@DisableNonlinearArithmetic
module Std.Arithmetic.GeneralInternals {

  /* this predicate is primarily used as a trigger */
  ghost predicate IsLe(x: int, y: int)
  {
    x <= y
  }

  /* aids in the process of induction for modulus */
  lemma LemmaInductionHelper(n: int, f: int -> bool, x: int)
    requires n > 0
    requires forall i :: 0 <= i < n ==> f(i)
    requires forall i {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i {:trigger f(i), f(i - n)} :: i < n  && f(i) ==> f(i - n)
    ensures  f(x)
    decreases if x >= n then x else -x
  {
    if (x >= n)
    {
      LemmaInductionHelper(n, f, x - n);
      assert f((x - n) + n);
    }
    else if (x < 0)
    {
      LemmaInductionHelper(n, f, x + n);
      assert f((x + n) - n);
    }
  }
}

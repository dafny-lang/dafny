/*******************************************************************************
 *  Original: Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *  
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/* lemmas and functions in this file are used in the proofs in Mul.dfy */

@DisableNonlinearArithmetic
module Std.Arithmetic.MulInternals {

  import opened GeneralInternals
  import opened MulInternalsNonlinear

  /* performs multiplication for positive integers using recursive addition */
  function MulPos(x: int, y: int) : int
    requires x >= 0
  {
    if x == 0 then 0
    else y + MulPos(x - 1, y)
  }

  /* performs multiplication for both positive and negative integers */
  function MulRecursive(x: int, y: int) : int
  {
    if x >= 0 then MulPos(x, y)
    else -1 * MulPos(-1 * x, y)
  }

  /* performs induction on multiplication */
  lemma LemmaMulInduction(f: int -> bool)
    requires f(0)
    requires forall i {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    requires forall i {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    forall i ensures f(i) { LemmaInductionHelper(1, f, i); }
  }

  /* proves that multiplication is always commutative */
  lemma LemmaMulCommutes()
    ensures  forall x:int, y:int {:trigger x * y} :: x * y == y * x
  {
    forall x:int, y:int
      ensures x * y == y * x
    {
      LemmaMulInduction(i => x * i == i * x);
    }
  }

  /* proves the distributive property of multiplication when multiplying an interger
  by (x +/- 1) */
  //rename for both directions ???
  lemma LemmaMulSuccessor()
    ensures forall x:int, y:int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    ensures forall x:int, y:int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
  {
    LemmaMulCommutes();
    forall x:int, y:int
      ensures (x + 1) * y == x * y + y
      ensures (x - 1) * y == x * y - y
    {
      LemmaMulIsDistributiveAdd(y, x, 1);
      LemmaMulIsDistributiveAdd(y, x, -1);
    }
  }

  /* proves the distributive property of multiplication */
  lemma LemmaMulDistributes()
    ensures forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    ensures forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
    LemmaMulSuccessor();
    forall x:int, y:int, z:int
      ensures (x + y) * z == x * z + y * z
      ensures (x - y) * z == x * z - y * z
    {
      var f1 := i => (x + i) * z == x * z + i * z;
      var f2 := i => (x - i) * z == x * z - i * z;
      assert forall i {:trigger (x + (i + 1)) * z} :: (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z;
      assert forall i {:trigger (x + (i - 1)) * z} :: (x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z;
      assert forall i {:trigger (x - (i + 1)) * z} :: (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z;
      assert forall i {:trigger (x - (i - 1)) * z} :: (x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z;
      LemmaMulInduction(f1);
      LemmaMulInduction(f2);
      assert f1(y);
      assert f2(y);
    }
  }

  /* groups distributive and associative properties of multiplication */
  ghost predicate MulAuto()
  {
    && (forall x:int, y:int {:trigger x * y} :: x * y == y * x)
    && (forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z)
    && (forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z)
  }

  /* proves that MulAuto is valid */
  lemma LemmaMulAuto()
    ensures  MulAuto()
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
  }

  /* performs auto induction for multiplication */
  lemma LemmaMulInductionAuto(x: int, f: int -> bool)
    requires MulAuto() ==> f(0)
                           && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1))
                           && (forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1))
    ensures  MulAuto()
    ensures  f(x)
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
    assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    LemmaMulInduction(f);
    assert f(x);
  }

  /* performs auto induction on multiplication for all i s.t. f(i) exists */
  lemma LemmaMulInductionAutoForall(f: int -> bool)
    requires MulAuto() ==> f(0)
                           && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1))
                           && (forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1))
    ensures  MulAuto()
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
    assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    LemmaMulInduction(f);
  }

}

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

@DisableNonlinearArithmetic
module Std.Arithmetic.Mul {

  import MulINL = MulInternalsNonlinear
  import opened MulInternals

  /* the built-in syntax of multiplication results in the same product as multiplication 
  through recursive addition */
  lemma LemmaMulIsMulRecursive(x: int, y: int)
    ensures x * y == MulRecursive(x, y)
  {
    if (x >= 0) { LemmaMulIsMulPos(x, y); }
    if (x <= 0) { LemmaMulIsMulPos(-x, y); }
    LemmaMulAuto();
  }

  lemma LemmaMulIsMulRecursiveAuto()
    ensures forall x: int, y: int :: x * y == MulRecursive(x, y)
  {
    forall x: int, y: int
      ensures x * y == MulRecursive(x, y)
    {
      LemmaMulIsMulRecursive(x, y);
    }
  }

  /* the built-in syntax of multiplying two positive integers results in the same product as 
  MulPos, which is achieved by recursive addition */
  lemma LemmaMulIsMulPos(x: int, y: int)
    requires x >= 0
    ensures x * y == MulPos(x, y)
  {
    if x == 0 {
      assert MulPos(x, y) == 0;
    } else {
      calc {
        MulPos(x, y);
        y + MulPos(x - 1, y);
        { LemmaMulIsMulPos(x - 1, y); }
        y + (x - 1) * y;
        { LemmaMulDistributes(); }
        x * y;
      }
    }
  }

  /* ensures that the basic properties of multiplication, including the identity and zero properties */
  lemma LemmaMulBasics(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    ensures 1 * x == x
    ensures x * 1 == x
  {
  }

  lemma LemmaMulBasicsAuto()
    ensures forall x: int {:trigger 0 * x} :: 0 * x == 0
    ensures forall x: int {:trigger x * 0} :: x * 0 == 0
    ensures forall x: int {:trigger 1 * x} :: 1 * x == x
    ensures forall x: int {:trigger x * 1} :: x * 1 == x
  {
  }

  /* multiplying two nonzero integers will never result in 0 as the poduct */
  lemma LemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
  {
    MulINL.LemmaMulNonzero(x, y);
  }

  /* multiplying any two nonzero integers will never result in 0 as the poduct */
  lemma LemmaMulNonzeroAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
  {
    forall x: int, y: int
      ensures x * y != 0 <==> x != 0 && y != 0
    {
      LemmaMulNonzero(x, y);
    }
  }

  /* any integer multiplied by 0 results in a product of 0 */
  lemma LemmaMulByZeroIsZeroAuto()
    ensures forall x: int {:trigger 0 * x} {:trigger x * 0} :: x * 0 == 0 * x == 0
  {
    forall x: int {:trigger 0 * x} {:trigger x * 0}
      ensures x * 0 == 0 * x == 0
    {
      LemmaMulBasics(x);
    }
  }

  /* multiplication is associative */
  lemma LemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
  {
    MulINL.LemmaMulIsAssociative(x, y, z);
  }

  /* multiplication is always associative for all integers*/
  lemma LemmaMulIsAssociativeAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y * z)} {:trigger (x * y) * z}
              :: x * (y * z) == (x * y) * z
  {
    forall x: int, y: int, z: int
      ensures x * (y * z) == (x * y) * z
    {
      LemmaMulIsAssociative(x, y, z);
    }
  }

  /* multiplication is commutative */
  lemma LemmaMulIsCommutative(x: int, y: int)
    ensures x * y == y * x
  {
  }

  /* multiplication is always commutative for all integers */
  lemma LemmaMulIsCommutativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  /* the product of two integers is greater than the value of each individual integer */
  lemma LemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
  {
    MulINL.LemmaMulOrdering(x, y);
  }

  /* the product of two positive integers is always greater than the individual value of either 
  multiplied integer */
  lemma LemmaMulOrderingAuto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 != x && 0 != y && x * y >= 0) ==> x * y >= x && x * y >= y
  {
    forall x: int, y: int | 0 != x && 0 != y && x * y >= 0
      ensures x * y >= x && x * y >= y
    {
      LemmaMulOrdering(x, y);
    }
  }

  lemma LemmaMulEquality(x: int, y: int, z: int)
    requires x == y
    ensures x * z == y * z
  {}

  lemma LemmaMulEqualityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z } :: x == y ==> x * z == y * z
  {
    forall x: int, y: int, z: int | x == y
      ensures x * z == y * z
    {
      LemmaMulEquality(x, y, z);
    }
  }

  /* two integers that are multiplied by a positive number will maintain their numerical order */
  lemma LemmaMulInequality(x: int, y: int, z: int)
    requires x <= y
    requires z >= 0
    ensures  x * z <= y * z
  {
    LemmaMulInductionAuto(z, u => u >= 0 ==> x * u <= y * u);
  }

  /* any two integers that are multiplied by a positive number will maintain their numerical order */
  lemma LemmaMulInequalityAuto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
  {
    forall x: int, y: int, z: int | x <= y && z >= 0
      ensures x * z <= y * z
    {
      LemmaMulInequality(x, y, z);
    }
  }

  /* multiplying by a positive integer preserves inequality */
  lemma LemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures  x * z < y * z
  {
    MulINL.LemmaMulStrictInequality(x, y, z);
  }

  /* multiplying by a positive integer preserves inequality for all integers*/
  lemma LemmaMulStrictInequalityAuto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
  {
    forall x: int, y: int, z: int | x < y && z > 0
      ensures x * z < y * z
    {
      LemmaMulStrictInequality(x, y, z);
    }
  }

  /* the product of two bounded integers is less than or equal to the product of their upper bounds */
  lemma LemmaMulUpperBound(x: int, XBound: int, y: int, YBound: int)
    requires x <= XBound
    requires y <= YBound
    requires 0 <= x
    requires 0 <= y
    ensures x * y <= XBound * YBound
  {
    LemmaMulInequality(x, XBound, y);
    LemmaMulInequality(y, YBound, XBound);
  }

  lemma LemmaMulUpperBoundAuto()
    ensures forall x: int, XBound: int, y: int, YBound: int {:trigger x * y, XBound * YBound}
              :: x <= XBound && y <= YBound && 0 <= x && 0 <= y ==> x * y <= XBound * YBound
  {
    forall x: int, XBound: int, y: int, YBound: int | x <= XBound && y <= YBound && 0 <= x && 0 <= y
      ensures x * y <= XBound * YBound
    {
      LemmaMulUpperBound(x, XBound, y, YBound);
    }
  }

  /* the product of two strictly upper bounded integers is less than the product of their upper bounds */
  lemma LemmaMulStrictUpperBound(x: int, XBound: int, y: int, YBound: int)
    requires x < XBound
    requires y < YBound
    requires 0 < x
    requires 0 < y
    ensures x * y <= (XBound - 1) * (YBound - 1)
  {
    LemmaMulInequality(x, XBound - 1, y);
    LemmaMulInequality(y, YBound - 1, XBound - 1);
  }

  lemma LemmaMulStrictUpperBoundAuto()
    ensures forall x: int, XBound: int, y: int, YBound: int {:trigger x * y, (XBound - 1) * (YBound - 1)}
              :: x < XBound && y < YBound && 0 < x && 0 < y ==> x * y <= (XBound - 1) * (YBound - 1)
  {
    forall x: int, XBound: int, y: int, YBound: int
      // https://github.com/dafny-lang/dafny/issues/4771
      {:trigger (XBound - 1) * (YBound - 1), x * y}
      {:trigger YBound - 1, XBound - 1, 0 < y, 0 < x}
      {:trigger YBound - 1, 0 < y, x < XBound}
      {:trigger XBound - 1, 0 < x, y < YBound}
      {:trigger y < YBound, x < XBound}
      | x < XBound && y < YBound && 0 < x && 0 < y
      ensures x * y <= (XBound - 1) * (YBound - 1)
    {
      LemmaMulStrictUpperBound(x, XBound, y, YBound);
    }
  }

  /* any two integers that are multiplied by a positive number will maintain their numerical order */
  lemma LemmaMulLeftInequality(x: int, y: int, z: int)
    requires 0 < x
    ensures y <= z ==> x * y <= x * z
    ensures y < z ==> x * y < x * z
  {
    LemmaMulInductionAuto(x, u => u > 0 ==> y <= z ==> u * y <= u * z);
    LemmaMulInductionAuto(x, u => u > 0 ==> y < z ==> u * y < u * z);
  }

  lemma LemmaMulLeftInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y, x * z}
              :: x > 0 ==> (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
  {
    forall x: int, y: int, z: int | (y <= z || y < z) && 0 < x
      ensures (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
    {
      LemmaMulLeftInequality(x, y, z);
    }
  }

  /* if two seperate integers are each multiplied by a common integer and the products are equal, the 
    two original integers are equal */
  lemma LemmaMulEqualityConverse(m: int, x: int, y: int)
    requires m != 0
    requires m * x == m * y
    ensures x == y
  {
    LemmaMulInductionAuto(m, u => x > y && 0 < u ==> x * u > y * u);
    LemmaMulInductionAuto(m, u => x > y && 0 > u ==> x * u < y * u);
    LemmaMulInductionAuto(m, u => x < y && 0 < u ==> x * u < y * u);
    LemmaMulInductionAuto(m, u => x < y && 0 > u ==> x * u > y * u);
  }

  /* if any two seperate integers are each multiplied by a common integer and the products are equal, the 
  two original integers are equal */
  lemma LemmaMulEqualityConverseAuto()
    ensures forall m: int, x: int, y: int {:trigger m * x, m * y} :: (m != 0 && m * x == m * y) ==> x == y
  {
    forall m: int, x: int, y: int | m != 0 && m * x == m * y
      ensures x == y
    {
      LemmaMulEqualityConverse(m, x, y);
    }
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z */
  lemma LemmaMulInequalityConverse(x: int, y: int, z: int)
    requires x * z <= y * z
    requires z > 0
    ensures  x <= y
  {
    LemmaMulInductionAuto(z, u => x * u <= y * u && u > 0 ==> x <= y);
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z 
  for all valid values of x, y, and z*/
  lemma LemmaMulInequalityConverseAuto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z <= y * z && z > 0 ==> x <= y
  {
    forall x: int, y: int, z: int | x * z <= y * z && z > 0
      ensures x <= y
    {
      LemmaMulInequalityConverse(x, y, z);
    }
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z */
  lemma LemmaMulStrictInequalityConverse(x: int, y: int, z: int)
    requires x * z < y * z
    requires z >= 0
    ensures  x < y
  {
    LemmaMulInductionAuto(z, u => x * u < y * u && u >= 0 ==> x < y);
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z 
  for all valid values of x, y, and z*/
  lemma LemmaMulStrictInequalityConverseAuto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z < y * z && z >= 0 ==> x < y
  {
    forall x: int, y: int, z: int | x * z < y * z && z >= 0
      ensures x < y
    {
      LemmaMulStrictInequalityConverse(x, y, z);
    }
  }

  /* multiplication is distributive */
  lemma LemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  {
    MulINL.LemmaMulIsDistributiveAdd(x, y, z);
  }

  /* for all integers, multiplication is distributive with addition in the form x * (y + z) */
  lemma LemmaMulIsDistributiveAddAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
  {
    forall x: int, y: int, z: int
      ensures x * (y + z) == x * y + x * z
    {
      LemmaMulIsDistributiveAdd(x, y, z);
    }
  }

  /* for all integers, multiplication is distributive with addition in the form (y + z) * x */
  lemma LemmaMulIsDistributiveAddOtherWay(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
  {
    LemmaMulAuto();
  }

  lemma LemmaMulIsDistributiveAddOtherWayAuto()
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
  {
    forall x: int, y: int, z: int
      ensures (y+z) * x == y * x + z * x
    {
      LemmaMulIsDistributiveAddOtherWay(x, y, z);
    }
  }

  /* multiplication is distributive with subtraction */
  lemma LemmaMulIsDistributiveSub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
  {
    LemmaMulAuto();
  }

  /* for all integers, multiplication is distributive with subtraction */
  lemma LemmaMulIsDistributiveSubAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
  {
    forall x: int, y: int, z: int
      ensures x * (y - z) == x * y - x * z
    {
      LemmaMulIsDistributiveSub(x, y, z);
    }
  }

  /* proves the overall distributive nature of multiplication*/
  lemma LemmaMulIsDistributive(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    ensures x * (y - z) == x * y - x * z
    ensures (y + z) * x == y * x + z * x
    ensures (y - z) * x == y * x - z * x
    ensures x * (y + z) == (y + z) * x
    ensures x * (y - z) == (y - z) * x
    ensures x * y == y * x
    ensures x * z == z * x
  {
    LemmaMulAuto();
  }

  /* for all integers, multiplication is distributive */
  lemma LemmaMulIsDistributiveAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
  {
    LemmaMulIsDistributiveAddAuto();
    LemmaMulIsDistributiveSubAuto();
    LemmaMulIsCommutativeAuto();
  }

  /* multiplying two positive integers will result in a positive integer */
  lemma LemmaMulStrictlyPositive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
  {
    MulINL.LemmaMulStrictlyPositive(x, y);
  }

  /* multiplying any two positive integers will result in a positive integer */
  lemma LemmaMulStrictlyPositiveAuto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (0 < x * y)
  {
    forall x: int, y: int | 0 < x && 0 < y
      ensures 0 < x * y
    {
      LemmaMulStrictlyPositive(x,y);
    }
  }

  /* multiplying a positive integer by an integer greater than 1 will result in a product that 
  is greater than the original integer */
  lemma LemmaMulStrictlyIncreases(x: int, y: int)
    requires 1 < x
    requires 0 < y
    ensures y < x * y
  {
    LemmaMulInductionAuto(x, u => 1 < u ==> y < u * y);
  }

  /* multiplying any positive integer by any integer greater than 1 will result in a product that 
  is greater than the original integer */
  lemma LemmaMulStrictlyIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y  ==> y < x * y
  {
    forall x: int, y: int | 1 < x && 0 < y
      ensures y < x * y
    {
      LemmaMulStrictlyIncreases(x, y);
    }
  }

  /* multiplying an integer by a positive integer will result in a product that is greater than or
  equal to the original integer */
  lemma LemmaMulIncreases(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures y <= x * y
  {
    LemmaMulInductionAuto(x, u => 0 < u ==> y <= u * y);
  }

  /* multiplying any integer by any positive integer will result in a product that is greater than or
  equal to the original integer */
  lemma LemmaMulIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (y <= x * y)
  {
    forall x: int, y: int | 0 < x && 0 < y
      ensures y <= x * y
    {
      LemmaMulIncreases(x, y);
    }
  }

  /* multiplying two positive numbers will result in a positive product */
  lemma LemmaMulNonnegative(x: int, y: int)
    requires 0 <= x
    requires 0 <= y
    ensures  0 <= x * y
  {
    LemmaMulInductionAuto(x, u => 0 <= u ==> 0 <= u * y);
  }

  /* multiplying any two positive numbers will result in a positive product */
  lemma LemmaMulNonnegativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
  {
    forall x: int, y: int | 0 <= x && 0 <= y
      ensures 0 <= x * y
    {
      LemmaMulNonnegative(x, y);
    }
  }

  /* shows the equivalent forms of using the unary negation operator */
  lemma LemmaMulUnaryNegation(x: int, y: int)
    ensures (-x) * y == -(x * y) == x * (-y)
  {
    LemmaMulInductionAuto(x, u => (-u) * y == -(u * y) == u * (-y));
  }

  /* shows the equivalent forms of using the unary negation operator for any integers*/
  lemma LemmaMulUnaryNegationAuto()
    ensures forall x: int, y: int {:trigger (-x) * y} {:trigger x * (-y)} :: (-x) * y == -(x * y) == x * (-y)
  {
    forall x: int, y: int
      ensures (-x) * y == -(x * y) == x * (-y)
    {
      LemmaMulUnaryNegation(x, y);
    }
  }

  /* multiplying two negative integers, -x and -y, is equivalent to multiplying x and y */
  lemma LemmaMulCancelsNegatives(x: int, y: int)
    ensures x * y == (-x) * (-y)
  {
    LemmaMulUnaryNegationAuto();
  }

  /* multiplying two negative integers, -x and -y, is equivalent to multiplying x and y */
  lemma LemmaMulCancelsNegativesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == (-x) * (-y)
  {
    forall x: int, y: int
      ensures x * y == (-x) * (-y)
    {
      LemmaMulCancelsNegatives(x, y);
    }
  }

  /* includes all properties of multiplication */
  lemma LemmaMulProperties()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
    ensures forall x: int {:trigger x * 1}{:trigger 1 * x} :: x * 1 == 1 * x == x
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
    ensures forall x: int, y: int, z: int {:trigger x * (y * z)}{:trigger (x * y) * z} :: x * (y * z) == (x * y) * z
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y && 0 <= x * y ==> x <= x * y && y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: (1 < x && 0 < y) ==> (y < x * y)
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (y <= x * y)
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (0 < x * y)
  {
    LemmaMulStrictInequalityAuto();
    LemmaMulInequalityAuto();
    LemmaMulIsDistributiveAuto();
    LemmaMulIsAssociativeAuto();
    LemmaMulOrderingAuto();
    LemmaMulNonzeroAuto();
    LemmaMulNonnegativeAuto();
    LemmaMulStrictlyIncreasesAuto();
    LemmaMulIncreasesAuto();
  }

}

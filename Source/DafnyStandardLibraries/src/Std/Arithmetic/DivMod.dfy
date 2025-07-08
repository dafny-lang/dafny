/*******************************************************************************
 *  Original: Copyright (c) Microsoft Corporation
 *  SPDX-License-Identifier: MIT
 *  
 *  Modifications and Extensions: Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/* Every lemma comes in 2 forms: 'LemmaProperty' and 'LemmaPropertyAuto'. The
former takes arguments and may be more stable and less reliant on Z3
heuristics. The latter includes automation and its use requires less effort*/

@DisableNonlinearArithmetic
module Std.Arithmetic.DivMod {

  import opened DivInternals
  import DivINL = DivInternalsNonlinear
  import opened ModInternals
  import ModINL = ModInternalsNonlinear
  import opened MulInternals
  import opened Mul
  import opened GeneralInternals

  /*****************************************************************************
   * Division:
   *****************************************************************************/

  /* the common syntax of division gives the same quotient as performing division through recursion */
  lemma LemmaDivIsDivRecursive(x: int, d: int)
    requires 0 < d
    ensures DivRecursive(x, d) == x / d
  {
    LemmaDivInductionAuto(d, x, u => DivRecursive(u, d) == u / d);
  }

  lemma LemmaDivIsDivRecursiveAuto()
    ensures forall x: int, d: int {:trigger x / d} :: d > 0 ==> DivRecursive(x, d) == x / d
  {
    forall x: int, d: int | d > 0
      ensures DivRecursive(x, d) == x / d
    {
      LemmaDivIsDivRecursive(x, d);
    }
  }

  /* the quotient of an integer divided by itself is 1 */
  lemma LemmaDivBySelf(d: int)
    requires d != 0
    ensures d / d == 1
  {
    DivINL.LemmaDivBySelf(d);
  }

  /* zero divided by an integer besides 0 is 0 */
  lemma LemmaDivOf0(d: int)
    requires d != 0
    ensures 0 / d == 0
  {
    DivINL.LemmaDivOf0(d);
  }

  /* ensures the basic propoerties of division: 0 divided by any integer is 0; any integer 
  divided by 1 is itself; any integer divided by itself is 1 */
  lemma LemmaDivBasics(x: int)
    ensures x != 0 ==> 0 / x == 0
    ensures x / 1 == x
    ensures x != 0 ==> x / x == 1
  {
    if x != 0 {
      LemmaDivBySelf(x);
      LemmaDivOf0(x);
    }
  }

  lemma LemmaDivBasicsAuto()
    ensures forall x {:trigger 0 / x} :: x != 0 ==> 0 / x == 0
    ensures forall x {:trigger x / 1} :: x / 1 == x
    ensures forall x, y {:trigger x / y} :: x >= 0 && y > 0 ==> x / y >= 0
    ensures forall x, y {:trigger x / y} :: x >= 0 && y > 0 ==> x / y <= x
  {
    forall x: int
      ensures x != 0 ==> 0 / x == 0
      ensures x / 1 == x
    {
      LemmaDivBasics(x);
    }
    forall x: int, y: int | x >= 0 && y > 0
      ensures 0 <= x / y <= x
    {
      LemmaDivPosIsPos(x, y);
      LemmaDivIsOrderedByDenominator(x, 1, y);
    }
  }

  /* if a dividend is a whole number and the divisor is a natural number and their
  quotient is 0, this implies that the dividend is smaller than the divisor */
  lemma LemmaSmallDivConverseAuto()
    ensures forall x, d {:trigger x / d } :: 0 <= x && 0 < d && x / d == 0 ==> x < d
  {
    forall x, d | 0 <= x && 0 < d && x / d == 0
      ensures x < d
    {
      LemmaDivInductionAuto(d, x, u => 0 <= u && 0 < d && u / d == 0 ==> u < d);
    }
  }

  lemma LemmaDivNonZero(x: int, d: int)
    requires x >= d > 0
    ensures x / d > 0
  {
    LemmaDivPosIsPosAuto();
    if x / d == 0 {
      LemmaSmallDivConverseAuto();
    }
  }

  lemma LemmaDivNonZeroAuto()
    ensures forall x, d {:trigger x / d } | x >= d > 0 :: x / d > 0
  {
    forall x, d | x >= d > 0 { LemmaDivNonZero(x, d); }
  }

  /* given two fractions with the same numerator, the order of numbers is determined by 
  the denominators. However, if the numerator is 0, the fractions are equal regardless of 
  the denominators' values */
  lemma LemmaDivIsOrderedByDenominator(x: int, y: int, z: int)
    requires 0 <= x
    requires 1 <= y <= z
    ensures x / y >= x / z
    decreases x
  {
    LemmaDivIsDivRecursiveAuto();
    assert forall u: int, d: int {:trigger u / d} {:trigger DivRecursive(u, d)}
        :: d > 0 ==> DivRecursive(u, d) == u / d;

    if x < z {
      LemmaDivIsOrdered(0, x, y);
    } else {
      LemmaDivIsOrdered(x - z, x - y, y);
      LemmaDivIsOrderedByDenominator(x - z, y, z);
    }
  }

  lemma LemmaDivIsOrderedByDenominatorAuto()
    ensures forall x: int, y: int, z: int {:trigger x / y, x / z} :: 0 <= x && 1 <= y <= z ==> x / y >= x / z
  {
    forall x: int, y: int, z: int | 0 <= x && 1 <= y <= z
      ensures x / y >= x / z
    {
      LemmaDivIsOrderedByDenominator(x, y, z);
    }
  }

  /* given two fractions with the same numerator, the order of numbers is strictly determined by 
  the denominators.*/
  lemma LemmaDivIsStrictlyOrderedByDenominator(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d  < x
    decreases x
  {
    LemmaDivInductionAuto(d, x, u => 0 < u ==> u / d < u);
  }

  lemma LemmaDivIsStrictlyOrderedByDenominatorAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
    forall x: int, d: int | 0 < x && 1 < d
      ensures x / d < x
    {
      LemmaDivIsStrictlyOrderedByDenominator(x, d);
    }
  }

  /* Rounding is different when multiplying the sum of two integers by a fraction d/d vs. 
  first multiplying each integer by d/d and then adding the quotients */
  lemma LemmaDividingSums(a: int, b: int, d: int, R: int)
    requires 0 < d
    requires R == a % d + b % d - (a + b) % d
    ensures d * ((a + b) / d) - R == d * (a / d) + d * (b / d)
  {
    calc ==> {
      a % d + b % d == R + (a + b) % d;
      (a + b) - (a + b) % d - R == a - (a % d) + b - (b % d);
      {
        LemmaFundamentalDivMod(a + b, d);
        LemmaFundamentalDivMod(a, d);
        LemmaFundamentalDivMod(b, d);
      }
      d * ((a + b) / d) - R == d * (a / d) + d * (b / d);
    }
  }

  lemma LemmaDividingSumsAuto()
    ensures forall a: int, b: int, d: int, R: int {:trigger d * ((a + b) / d) - R, d*(a/d) + d*(b/d)}
              :: 0 < d &&  R == a%d + b%d - (a+b)%d ==> d*((a+b)/d) - R == d*(a/d) + d*(b/d)
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall a: int, b: int, d: int, R: int {:trigger d * ((a + b) / d) - R, d*(a/d) + d*(b/d)} | 0< d &&  R == a%d + b%d - (a+b)%d
      ensures d*((a+b)/d) - R == d*(a/d) + d*(b/d)
    {
      LemmaDividingSums(a, b, d, R);
    }
  }

  /* dividing a whole number by a natural number will result in a quotient that is 
  greater than or equal to 0 */
  lemma LemmaDivPosIsPos(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x / d
  {
    LemmaDivInductionAuto(d, x, u => 0 <= u ==> u / d >= 0);
  }

  lemma LemmaDivPosIsPosAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> 0 <= x / d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures 0 <= x / d
    {
      LemmaDivPosIsPos(x, d);
    }
  }

  /* dividing an integer and then adding 1 to the quotient is the same as adding 
  the divisor and the integer, and then dividing that sum by the divisor */
  lemma LemmaDivPlusOne(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
  {
    LemmaDivAuto(d);
  }

  lemma LemmaDivPlusOneAuto()
    ensures forall x: int, d: int {:trigger 1 + x / d, (d + x) / d} :: 0 < d ==> 1 + x / d == (d + x) / d
  {
    forall x: int, d: int | 0 < d
      ensures 1 + x / d == (d + x) / d
    {
      LemmaDivPlusOne(x, d);
    }
  }

  /* dividing an integer and then subtracting 1 from the quotient is the same as subtracting 
  the divisor from the integer, and then dividing that difference by the divisor */
  lemma LemmaDivMinusOne(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
  {
    LemmaDivAuto(d);
  }

  lemma LemmaDivMinusOneAuto()
    ensures forall x: int, d: int {:trigger -1 + x / d, (-d + x) / d} :: 0 < d ==> -1 + x / d == (-d + x) / d
  {
    forall x: int, d: int | 0 < d
      ensures -1 + x / d == (-d + x) / d
    {
      LemmaDivMinusOne(x, d);
    }
  }

  /* dividing a smaller integer by a larger integer results in a quotient of 0 */
  lemma LemmaBasicDiv(d: int)
    requires 0 < d
    ensures forall x {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
    LemmaDivAuto(d);
  }

  lemma LemmaBasicDivAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
    forall x: int, d: int | 0 <= x < d
      ensures x / d == 0
    {
      LemmaBasicDiv(d);
    }
  }

  /* numerical order is preserved when dividing two seperate integers by a common positive divisor */
  lemma LemmaDivIsOrdered(x: int, y: int, z: int)
    requires x <= y
    requires 0 < z
    ensures x / z <= y / z
  {
    LemmaDivInductionAuto(z, x - y, xy => xy <= 0 ==> (xy + y) / z <= y / z);
  }

  lemma LemmaDivIsOrderedAuto()
    ensures forall x: int, y: int, z: int {:trigger x / z, y / z} :: x <= y && 0 < z ==> x / z <= y / z
  {
    forall x: int, y: int, z: int | x <= y && 0 < z
      ensures x / z <= y / z
    {
      LemmaDivIsOrdered(x, y, z);
    }
  }

  /* dividing an integer by 2 or more results in a quotient that is smaller than the 
  original dividend */
  lemma LemmaDivDecreases(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d  < x
  {
    LemmaDivInductionAuto(d, x, u => 0 < u ==> u / d < u);
  }

  lemma LemmaDivDecreasesAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
    forall x: int, d: int | 0 < x && 1 < d
      ensures x / d < x
    {
      LemmaDivDecreases(x, d);
    }
  }

  /* dividing an integer by 1 or more results in a quotient that is less than or equal to 
  the original dividend */
  lemma LemmaDivNonincreasing(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x / d  <= x
  {
    LemmaDivInductionAuto(d, x, u => 0 <= u ==> u / d <= u);
  }

  lemma LemmaDivNonincreasingAuto()
    ensures forall x: int, d: int {:trigger x / d } :: 0 <= x && 0 < d ==> x / d <= x
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures x / d <= x
    {
      LemmaDivNonincreasing(x, d);
    }
  }

  /* a natural number x divided by a larger natural number gives a remainder equal to x */
  lemma LemmaSmallMod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
  {
    ModINL.LemmaSmallMod(x, m);
  }

  lemma LemmaBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures 0 < y * z
    ensures x % (y * z) ==y * ((x / y) % z) + x % y
  {
    LemmaMulStrictlyPositiveAuto();
    LemmaDivPosIsPos(x, y);
    assert 0 <= x / y;

    calc {
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
    <=    { LemmaPartBound1(x, y, z); }
      y * (z - 1) + (x % y) % (y * z);
    <    { LemmaPartBound2(x, y, z); }
      y * (z - 1) + y;
          { LemmaMulBasicsAuto(); }
      y * (z - 1) + y * 1;
          { LemmaMulIsDistributiveAuto(); }
      y * (z - 1 + 1);
      y * z;
    }

    calc {
      x % (y * z);
      { LemmaFundamentalDivMod(x,y); }
      (y * (x / y) + x % y) % (y * z);
      {
        LemmaModPropertiesAuto();
        assert 0 <= x % y;
        LemmaMulNonnegative(y, x / y);
        assert (y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z;
        LemmaModAdds(y * (x / y), x % y, y * z);
      }
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
      {
        LemmaModPropertiesAuto();
        LemmaMulIncreases(z, y);
        LemmaMulIsCommutativeAuto();
        assert x % y < y <= y * z;
        LemmaSmallMod(x % y, y * z);
        assert (x % y) % (y * z) == x % y;
      }
      (y * (x / y)) % (y * z) + x % y;
      { LemmaTruncateMiddle(x / y, y, z); }
      y * ((x / y) % z) + x % y;
    }
  }

  lemma LemmaBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % (y * z), y * ((x / y) % z) + x % y}
              :: 0 <= x && 0 < y && 0 < z ==> 0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y
  {
    forall x: int, y: int, z: int  | 0 <= x && 0 < y && 0 < z
      ensures 0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y
    {
      LemmaBreakdown(x, y, z);
    }
  }

  lemma LemmaRemainderUpper(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x - d < x / d * d
  {
    LemmaMulAuto();
    LemmaDivInductionAuto(d, x, u => 0 <= u ==> u - d < u / d * d);
  }

  lemma LemmaRemainderUpperAuto()
    ensures forall x: int, d: int {:trigger x - d, d * d} :: 0 <= x && 0 < d ==> x - d < x / d * d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures x - d < x / d * d
    {
      LemmaRemainderUpper(x, d);
    }
  }

  lemma LemmaRemainderLower(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures  x >= x / d * d
  {
    LemmaMulAuto();
    LemmaDivInductionAuto(d, x, u => 0 <= u ==> u >= u / d * d);
  }

  lemma LemmaRemainderLowerAuto()
    ensures forall x: int, d: int {:trigger x / d * d} :: 0 <= x && 0 < d ==> x >= x / d * d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures x >= x / d * d
    {
      LemmaRemainderLower(x, d);
    }
  }

  lemma LemmaRemainder(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures  0 <= x - (x / d * d) < d
  {
    LemmaMulAuto();
    LemmaDivInductionAuto(d, x, u => 0 <= u - u / d * d < d);
  }

  lemma LemmaRemainderAuto()
    ensures forall x: int, d: int {:trigger x - (x / d * d)} :: 0 <= x && 0 < d ==> 0 <= x - (x / d * d) < d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures 0 <= x - (x / d * d) < d
    {
      LemmaRemainder(x, d);
    }
  }

  /* describes fundementals of the modulus operator */
  lemma LemmaFundamentalDivMod(x: int, d: int)
    requires d != 0
    ensures x == d * (x / d) + (x % d)
  {
    ModINL.LemmaFundamentalDivMod(x, d);
  }

  lemma LemmaFundamentalDivModAuto()
    ensures forall x: int, d: int {:trigger d * (x / d) + (x % d)} :: d != 0 ==> x == d * (x / d) + (x % d)
  {
    forall x: int, d: int | d != 0
      ensures x == d * (x / d) + (x % d)
    {
      LemmaFundamentalDivMod(x, d);
    }
  }

  /* dividing a fraction by a divisor is equivalent to multiplying the fraction's 
  denominator with the divisor */
  lemma LemmaDivDenominator(x: int,c: nat,d: nat)
    requires 0 <= x
    requires 0 < c
    requires 0 < d
    ensures c * d != 0
    ensures (x / c) / d == x / (c * d)
  {
    LemmaMulStrictlyPositiveAuto();
    var R := x % (c * d);
    LemmaModPropertiesAuto();

    LemmaDivPosIsPos(R, c);
    if R / c >= d {
      LemmaFundamentalDivMod(R, c);
      LemmaMulInequality(d, R / c, c);
      LemmaMulIsCommutativeAuto();
      assert false;
    }
    assert R / c < d;

    LemmaMulBasicsAuto();
    LemmaFundamentalDivModConverse(R / c, d, 0, R / c);
    assert (R / c) % d == R / c;

    LemmaFundamentalDivMod(R, c);
    assert c * (R / c) + R % c == R;

    assert c * ((R / c) % d) + R % c == R;

    var k := x / (c * d);
    LemmaFundamentalDivMod(x, c * d);
    assert x == (c * d) * (x / (c * d)) + x % (c * d);
    assert R == x - (c * d) * (x / (c * d));
    assert R == x - (c * d) * k;

    calc {
      c * ((x / c) % d) + x % c;
      { LemmaModMultiplesVanish(-k, x / c, d); LemmaMulIsCommutativeAuto(); }
      c * ((x / c + (-k) * d) % d) + x % c;
      { LemmaHoistOverDenominator(x, (-k)*d, c); }
      c * (((x + (((-k) * d) * c)) / c) % d) + x % c;
      { LemmaMulIsAssociative(-k, d, c); }
      c * (((x + ((-k) * (d * c))) / c) % d) + x % c;
      { LemmaMulUnaryNegation(k, d * c); }
      c * (((x + (-(k * (d * c)))) / c) % d) + x % c;
      { LemmaMulIsAssociative(k, d, c); }
      c * (((x + (-(k * d * c))) / c) % d) + x % c;
      c * (((x - k * d * c) / c) % d) + x % c;
      {
        LemmaMulIsAssociativeAuto();
        LemmaMulIsCommutativeAuto();
      }
      c * ((R / c) % d) + x % c;
      c * (R / c) + x % c;
      { LemmaFundamentalDivMod(R, c);
        assert R == c * (R / c) + R % c;
        LemmaModMod(x, c, d);
        assert R % c == x % c;
      }
      R;
      { LemmaModIsModRecursiveAuto(); }
      R % (c * d);
      (x - (c * d) * k) % (c * d);
      { LemmaMulUnaryNegation(c * d, k); }
      (x + (c * d) * (-k)) % (c * d);
      { LemmaModMultiplesVanish(-k, x, c * d); }
      x % (c * d);
    }
    calc ==> {
      c * (x / c) + x % c - R == c * (x / c) - c * ((x / c) % d);
      { LemmaFundamentalDivMod(x, c); }
      x - R == c * (x / c) - c * ((x / c) % d);
    }
    calc ==> {
      true;
      { LemmaFundamentalDivMod(x / c, d); }
      d * ((x / c) / d) == x / c - ((x / c) % d);
      c * (d * ((x / c) / d)) == c * (x / c - ((x / c) % d));
      { LemmaMulIsAssociativeAuto(); }
      (c * d) * ((x / c) / d) == c * (x / c - ((x / c) % d));
      { LemmaMulIsDistributiveAuto(); }
      (c * d) * ((x / c) / d) == c * (x / c) - c * ((x / c) % d);
      (c * d) * ((x / c) / d) == x - R;
      { LemmaFundamentalDivMod(x, c * d); }
      (c * d) * ((x / c) / d) == (c * d) * (x / (c * d)) + x % (c * d) - R;
      (c * d) * ((x / c) / d) == (c * d) * (x / (c * d));
      { LemmaMulEqualityConverse(c * d, (x / c) / d, x / (c * d)); }
      (x / c) / d == x / (c * d);
    }
  }

  lemma LemmaDivDenominatorAuto()
    ensures forall c: nat, d: nat {:trigger c * d} :: 0 < c && 0 < d ==> c * d != 0
    ensures forall x: int, c: nat, d: nat {:trigger (x / c) / d}
              :: 0 <= x && 0 < c && 0 < d ==> (x / c) / d == x / (c * d)
  {
    LemmaMulNonzeroAuto();
    forall x: int, c: nat, d: nat | 0 <= x && 0 < c && 0 < d
      ensures (x / c) / d == x / (c * d)
    {
      LemmaDivDenominator(x, c, d);
    }
  }

  /* multiplying an integer by a fraction is equivalent to multiplying the integer by the
  fraction's numerator */
  lemma LemmaMulHoistInequality(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < z
    ensures x * (y / z) <= (x * y) / z
  {
    calc {
      (x * y) / z;
        { LemmaFundamentalDivMod(y, z); }
      (x * (z * (y / z) + y % z)) / z;
        { LemmaMulIsDistributiveAuto(); }
      (x * (z * (y / z)) + x * (y % z)) / z;
    >=  {
          LemmaModPropertiesAuto();
          LemmaMulNonnegative(x, y % z);
          LemmaDivIsOrdered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z); }
      (x * (z * (y / z))) / z;
        { LemmaMulIsAssociativeAuto();
          LemmaMulIsCommutativeAuto(); }
      (z * (x * (y / z))) / z;
        { LemmaDivMultiplesVanish(x * (y / z), z); }
      x * (y / z);
    }
  }

  lemma LemmaMulHoistInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y / z), (x * y) / z}
              :: 0 <= x && 0 < z ==> x * (y / z) <= (x * y) / z
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < z
      ensures x * (y / z) <= (x * y) / z
    {
      LemmaMulHoistInequality(x, y, z);
    }
  }

  lemma {:induction false} LemmaIndistinguishableQuotients(a: int, b: int, d: int)
    requires 0 < d
    requires 0 <= a - a % d <= b < a + d - a % d
    ensures a / d == b / d
  {
    var f := ab => var u := ab + b; 0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d;
    assert f(a - b) by {
      LemmaDivInductionAuto(d, a - b, f);
    }
  }

  lemma LemmaIndistinguishableQuotientsAuto()
    ensures forall a: int, b: int, d: int {:trigger a / d, b / d}
              :: 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> a / d == b / d
  {
    forall a: int, b: int, d: int | 0 < d && 0 <= a - a % d <= b < a + d - a % d
      ensures a / d == b / d
    {
      LemmaIndistinguishableQuotients(a, b, d);
    }
  }

  /* common factors from the dividend and divisor of a modulus operation can be factored out */
  lemma LemmaTruncateMiddle(x: int, b: int, c: int)
    requires 0 <= x
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures (b * x) % (b * c) == b * (x % c)
  {
    LemmaMulStrictlyPositiveAuto();
    LemmaMulNonnegativeAuto();
    calc {
      b * x;
      { LemmaFundamentalDivMod(b * x, b * c); }
      (b * c) * ((b * x) / (b * c)) + (b * x) % (b * c);
      { LemmaDivDenominator(b * x, b, c); }
      (b * c) * (((b * x) / b) / c) + (b * x) % (b * c);
      { LemmaMulIsCommutativeAuto(); LemmaDivByMultiple(x, b); }
      (b * c) * (x / c) + (b * x) % (b * c);
    }
    calc ==> {
      true;
      { LemmaFundamentalDivMod(x, c); }
      x == c * (x / c) + x % c;
      b * x == b * (c * (x / c) + x % c);
      { LemmaMulIsDistributiveAuto(); }
      b * x == b * (c * (x / c)) + b * (x % c);
      { LemmaMulIsAssociativeAuto(); }
      b * x == (b * c) * (x / c) + b * (x % c);
    }
  }

  lemma LemmaTruncateMiddleAuto()
    ensures forall x: int, b: int, c: int {:trigger b * (x % c)}
              :: 0 <= x && 0 < b && 0 < c && 0 < b * c ==> (b * x) % (b * c) == b * (x % c)
  {
    forall x: int, b: int, c: int | 0 <= x && 0 < b && 0 < c && 0 < b * c
      ensures (b * x) % (b * c) == b * (x % c)
    {
      LemmaTruncateMiddle(x, b, c);
    }
  }

  /* multiplying the numerator and denominator by an integer does not change the quotient */
  lemma LemmaDivMultiplesVanishQuotient(x: int, a: int, d: int)
    requires 0 < x
    requires 0 <= a
    requires 0 < d
    ensures 0 < x * d
    ensures a / d == (x * a) / (x * d)
  {
    LemmaMulStrictlyPositive(x,d);
    calc {
      (x * a) / (x * d);
      {
        LemmaMulNonnegative(x, a);
        LemmaDivDenominator(x * a, x, d); }
      ((x * a) / x) / d;
      { LemmaDivMultiplesVanish(a, x); }
      a / d;
    }
  }

  lemma LemmaDivMultiplesVanishQuotientAuto()
    ensures forall x: int, a: int, d: int {:trigger a / d, x * d, x * a}
              :: 0 < x && 0 <= a && 0 < d ==> 0 < x * d  &&  a / d == (x * a) / (x * d)
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall x: int, a: int, d: int {:trigger x * d, 0 <= a} | 0 < x && 0 <= a && 0 < d
      ensures 0 < x * d  &&  a / d == (x * a) / (x * d)
    {
      LemmaDivMultiplesVanishQuotient(x, a, d);
    }
  }

  /* rounds down when adding an integer r to the dividend a that is smaller than the divisor d, and then
  multiplying by d */
  lemma LemmaRoundDown(a: int, r: int, d: int)
    requires 0 < d
    requires a % d == 0
    requires 0 <= r < d
    ensures a == d * ((a + r) / d)
  {
    LemmaMulAuto();
    LemmaDivInductionAuto(d, a, u => u % d == 0 ==> u == d * ((u + r) / d));
  }

  lemma LemmaRoundDownAuto()
    ensures forall a: int, r: int, d: int {:trigger d * ((a + r) / d)}
              :: 0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d)
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall a: int, r: int, d: int {:trigger a + r, r < d} {:trigger a + r, 0 < d} {:trigger 0 <= r, a % d} | 0 < d && a % d == 0 && 0 <= r < d
      ensures a == d * ((a + r) / d)
    {
      LemmaRoundDown(a, r, d);
    }
  }

  /* this is the same as writing x + (b/d) == x when b is less than d; this is true because (b/d) == 0 */
  @IsolateAssertions
  lemma LemmaDivMultiplesVanishFancy(x: int, b: int, d: int)
    requires 0 < d
    requires 0 <= b < d
    ensures (d * x + b) / d == x
  {
    assert b/d == 0 by { LemmaDivAuto(d); }
    var f := u => (d * u + b) / d == u;
    assert f(0);
    forall i
      ensures IsLe(0, i) && f(i) ==> f(i + 1)
    {
      if f(i) {
        var z := ((d * i) + b) % d + d % d;
        assert 0 <= z < d;
        assert f (i + 1) by {
          calc {
            i + 1;
            ((d * i) + b)/d + d/d; {
              assert DivPlus (d, d * i + b, d) by {LemmaDivAuto(d);}
            }
            ((d * i) + b + d)/d; {
              LemmaMulAuto();
            }
            (d * (i + 1) + b)/d;
          }
        }
      }
    }
    forall i
      ensures IsLe(i, 0) && f(i) ==> f(i - 1)
    {
      if f(i) {
        var z := ((d * i) + b) % d - d % d;
        assert 0 <= z < d;
        assert f (i - 1) by {
          calc {
            i - 1;
            ((d * i) + b)/d - d/d; {
              assert DivMinus (d, d * i + b, d) by {LemmaDivAuto(d);}
            }
            ((d * i) + b - d)/d; {
              LemmaMulAuto();
            }
            (d * (i - 1) + b)/d;
          }
        }
      }
    }
    LemmaMulInductionAuto(x, f);
  }

  lemma LemmaDivMultiplesVanishFancyAuto()
    ensures forall x: int, b: int, d: int {:trigger (d * x + b) / d}
              :: 0 < d && 0 <= b < d ==> (d * x + b) / d == x
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall x: int, b: int, d: int {:trigger d * x, b < d} {:trigger d * x, 0 <= b} | 0 < d && 0 <= b < d
      ensures (d * x + b) / d == x
    {
      LemmaDivMultiplesVanishFancy(x, b, d);
    }
  }

  /* multiplying an integer by a common numerator and denominator results in the original integer */
  lemma LemmaDivMultiplesVanish(x: int, d: int)
    requires 0 < d
    ensures (d * x) / d == x
  {
    LemmaDivMultiplesVanishFancy(x, 0, d);
  }

  lemma LemmaDivMultiplesVanishAuto()
    ensures forall x: int, d: int {:trigger (d * x) / d} :: 0 < d ==> (d * x) / d == x
  {
    forall x: int, d: int | 0 < d
      ensures (d * x) / d == x
    {
      LemmaDivMultiplesVanish(x, d);
    }
  }

  /* multiplying a whole number by a common numerator and denominator results in the original integer */
  lemma LemmaDivByMultiple(b: int, d: int)
    requires 0 <= b
    requires 0 < d
    ensures  (b * d) / d == b
  {
    LemmaDivMultiplesVanish(b,d);
  }

  lemma LemmaDivByMultipleAuto()
    ensures forall b: int, d: int {:trigger (b * d) / d} :: 0 <= b && 0 < d ==> (b * d) / d == b
  {
    forall b: int, d: int | 0 <= b && 0 < d
      ensures (b * d) / d == b
    {
      LemmaDivByMultiple(b, d);
    }
  }

  /* a dividend y that is a positive multiple of the divisor z will always yield a greater quotient 
  than a dividend x that is less than y */
  lemma LemmaDivByMultipleIsStronglyOrdered(x: int, y: int, m: int, z: int)
    requires x < y
    requires y == m * z
    requires 0 < z
    ensures  x / z < y / z
  {
    LemmaModMultiplesBasic(m, z);
    LemmaDivInductionAuto(z, y - x, yx => var u := yx + x; x < u && u % z == 0 ==> x / z < u / z);
  }

  lemma LemmaDivByMultipleIsStronglyOrderedAuto()
    ensures forall x: int, y: int, m: int, z: int {:trigger x / z, m * z, y / z}
              :: x < y && y == m * z && 0 < z ==> x / z < y / z
  {
    forall x: int, y: int, m: int, z: int | x < y && y == m * z && 0 < z
      ensures x / z < y / z
    {
      LemmaDivByMultipleIsStronglyOrdered(x, y, m, z);
    }
  }

  /* if an integer a is less than or equal to the product of two other integers b and c, then the 
  quotient of a/b will be less than or equal to c */
  lemma LemmaMultiplyDivideLe(a: int, b: int, c: int)
    requires 0 < b
    requires a <= b * c
    ensures  a / b <= c
  {
    LemmaModMultiplesBasic(c, b);
    LemmaDivInductionAuto(b, b * c - a, i => 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b);
    LemmaDivMultiplesVanish(c, b);
  }

  lemma LemmaMultiplyDivideLeAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b , b * c} :: 0 < b && a <= b * c ==> a / b <= c
  {
    forall a: int, b: int, c: int | 0 < b && a <= b * c
      ensures a / b <= c
    {
      LemmaMultiplyDivideLe(a, b, c);
    }
  }

  /* if an integer a is less than the product of two other integers b and c, then the quotient 
  of a/b will be less than c */
  lemma LemmaMultiplyDivideLt(a: int, b: int, c: int)
    requires 0 < b
    requires a < b * c
    ensures  a / b < c
  {
    LemmaModMultiplesBasic(c, b);
    LemmaDivInductionAuto(b, b * c - a, i => 0 < i && (i + a) % b == 0 ==> a / b < (i + a) / b);
    LemmaDivMultiplesVanish(c, b);
  }

  lemma LemmaMultiplyDivideLtAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a < b * c ==> a / b < c
  {
    forall a: int, b: int, c: int | 0 < b && a < b * c
      ensures a / b < c
    {
      LemmaMultiplyDivideLt(a, b, c);
    }
  }

  /* expresses the equality of giving fractions common denominators and then adding them together */
  lemma LemmaHoistOverDenominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d + j == (x + j * d) / d
  {
    LemmaDivAuto(d);
    LemmaMulInductionAuto(j, u => x / d  + u == (x + u * d) / d);
  }

  lemma LemmaHoistOverDenominatorAuto()
    ensures forall x: int, j: int, d: nat {:trigger  x / d + j} :: 0 < d ==> x / d + j == (x + j * d) / d
  {
    forall x: int, j: int, d: nat | 0 < d
      ensures x / d + j == (x + j * d) / d
    {
      LemmaHoistOverDenominator(x, j, d);
    }
  }

  lemma LemmaPartBound1(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures (b * (a / b) % (b * c)) <= b * (c - 1)
  {
    LemmaMulStrictlyPositiveAuto();
    calc {
      b * (a / b) % (b * c);
      { LemmaFundamentalDivMod(b * (a / b), b * c); }
      b * (a / b) - (b * c) * ((b * (a / b)) / (b * c));
      { LemmaMulIsAssociativeAuto(); }
      b * (a / b) - b * (c * ((b * (a / b)) / (b * c)));
      { LemmaMulIsDistributiveAuto(); }
      b * ((a / b) - (c * ((b * (a / b)) / (b * c))));
    }

    calc ==> {
      true;
      { LemmaModPropertiesAuto(); }
      b * (a / b) % (b * c) < b * c;
      b * ((a / b) - (c * ((b * (a / b)) / (b * c)))) < b * c;
      { LemmaMulIsCommutativeAuto(); LemmaMulStrictInequalityConverseAuto(); }
      ((a / b) - (c * ((b * (a / b)) / (b * c)))) < c;
      ((a / b) - (c * ((b * (a / b)) / (b * c)))) <= c - 1;
      { LemmaMulIsCommutativeAuto(); LemmaMulInequalityAuto(); }
      b * ((a / b) - (c * ((b * (a / b)) / (b * c)))) <= b * (c - 1);
      b * (a / b) % (b * c) <= b * (c - 1);
    }
  }

  lemma LemmaPartBound1Auto()
    ensures forall a: int, b: int, c: int {:trigger b * (a / b) % (b * c)}
              :: 0 <= a && 0 < b && 0 < c ==> 0 < b * c && (b * (a / b) % (b * c)) <= b * (c - 1)
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall a: int, b: int, c: int {:trigger b * c, 0 <= a} | 0 <= a && 0 < b && 0 < c
      ensures 0 < b * c && (b * (a / b) % (b * c)) <= b * (c - 1)
    {
      LemmaPartBound1(a, b, c);
    }
  }


  /*******************************************************************************
   * Modulus:
   *******************************************************************************/

  /* the common syntax of the modulus operation results in the same remainder as recursively
  calculating the modulus */
  lemma LemmaModIsModRecursive(x: int, m: int)
    requires m > 0
    ensures ModRecursive(x, m) == x % m
    decreases if x < 0 then -x + m else x
  {
    if x < 0 {
      calc {
        ModRecursive(x, m);
        ModRecursive(x + m, m);
        { LemmaModIsModRecursive(x + m, m); }
        (x + m) % m;
        { LemmaAddModNoop(x, m, m); }
        ((x % m) + (m % m)) % m;
        { LemmaModBasicsAuto(); }
        (x % m) % m;
        { LemmaModBasicsAuto(); }
        x % m;
      }
    } else if x < m {
      LemmaSmallMod(x, m);
    } else {
      calc {
        ModRecursive(x, m);
        ModRecursive(x - m, m);
        { LemmaModIsModRecursive(x - m, m); }
        (x - m) % m;
        { LemmaSubModNoop(x, m, m); }
        ((x % m) - (m % m)) % m;
        { LemmaModBasicsAuto(); }
        (x % m) % m;
        { LemmaModBasicsAuto(); }
        x % m;
      }
    }
  }

  lemma LemmaModIsModRecursiveAuto()
    ensures forall x: int, d: int {:trigger x % d}:: d > 0 ==> ModRecursive(x, d) == x % d
  {
    forall x: int, d: int | d > 0
      ensures ModRecursive(x, d) == x % d
    {
      LemmaModIsModRecursive(x, d);
    }
  }

  /* proves basic properties of the modulus operation: any integer divided by itself does not have a
  remainder; performing (x % m) % m gives the same result as simply perfoming x % m  */
  lemma LemmaModBasicsAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger (x % m) % m} :: m > 0 ==> (x % m) % m == x % m
  {
    forall m: int | m > 0
      ensures m % m == 0
    {
      LemmaModAuto(m);
    }
    forall x: int, m: int | m > 0
      ensures (x % m) % m == x % m
    {
      LemmaModAuto(m);
    }
  }

  /* describes the properties of the modulus operation including those described in LemmaModBasicsAuto. 
  This lemma also states that the remainder of any division will be less than the divisor's value  */
  lemma LemmaModPropertiesAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger (x % m) % m} :: m > 0 ==> (x % m) % m == x % m
    ensures forall x: int, m: int {:trigger x % m} :: m > 0 ==> 0 <= x % m < m
  {
    LemmaModBasicsAuto();

    forall x: int, m: int | m > 0
      ensures 0 <= x % m < m
    {
      LemmaModAuto(m);
    }
  }

  /* the remainder of a natural number x divided by a natural number d will be less
  than or equal to x */
  lemma LemmaModDecreases(x: nat, m: nat)
    requires 0 < m
    ensures x % m <= x
  {
    LemmaModAuto(m);
  }

  lemma LemmaModDecreasesAuto()
    ensures forall x: nat, m: nat {:trigger x % m} :: 0 < m ==> x % m <= x
  {
    forall x: nat, m: nat | 0 < m
      ensures x % m <= x
    {
      LemmaModDecreases(x, m);
    }
  }

  /* if x % y is zero and x is greater than zero, x is greater than y. */
  lemma LemmaModIsZero(x: nat, m: nat)
    requires x > 0 && m > 0
    requires x % m == 0
    ensures x >= m
  {
    if x < m {
      assert x % m == x by { LemmaSmallMod(x, m); }
      assert false;
    }
  }

  lemma LemmaModIsZeroAuto()
    ensures forall x: nat, m: nat {:trigger x % m} :: (x > 0 && m > 0
                                                       && x % m == 0) ==> x >= m
  {
    forall x: nat, m: nat | x > 0 && m > 0 && x % m == 0
      ensures x >= m
    {
      LemmaModIsZero(x, m);
    }
  }

  /* a dividend that is any multiple of the divisor will result in a remainder of 0 */
  lemma LemmaModMultiplesBasic(x: int, m: int)
    requires m > 0
    ensures (x * m) % m == 0
  {
    LemmaModAuto(m);
    LemmaMulInductionAuto(x, u => (u * m) % m == 0);
  }

  lemma LemmaModMultiplesBasicAuto()
    ensures forall x: int, m: int {:trigger (x * m) % m} :: m > 0 ==> (x * m) % m == 0
  {
    forall x: int, m: int | m > 0
      ensures (x * m) % m == 0
    {
      LemmaModMultiplesBasic(x, m);
    }
  }

  /* the remainder of adding the divisor m to the dividend b will be the same
  as simply performing b % m */
  lemma LemmaModAddMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaModAddMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (m + b) % m == b % m
  {
    forall b: int, m: int | 0 < m
      ensures (m + b) % m == b % m
    {
      LemmaModAddMultiplesVanish(b, m);
    }
  }

  /* the remainder of subtracting the divisor m from the dividend b will be the same
  as simply performing b % m */
  lemma LemmaModSubMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaModSubMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (-m + b) % m == b % m
  {
    forall b: int, m: int | 0 < m
      ensures (-m + b) % m == b % m
    {
      LemmaModSubMultiplesVanish(b, m);
    }
  }

  predicate MultiplesVanish(a: int, b: int, m: int)
    requires 0 < m
  {
    (m * a + b) % m == b % m
  }

  /* the remainder of adding any multiple of the divisor m to the dividend b will be the same
  as simply performing b % m */
  lemma LemmaModMultiplesVanish(a: int, b: int, m: int)
    decreases if a > 0 then a else -a
    requires 0 < m
    ensures MultiplesVanish(a, b, m)
  {
    LemmaModAuto(m);
    LemmaMulAuto();
    assert MultiplesVanish(0, b, m);
    LemmaMulInductionAuto(a, u => MultiplesVanish(u, b, m));
  }

  lemma LemmaModMultiplesVanishAuto()
    ensures forall a: int, b: int, m: int {:trigger (m * a + b) % m} :: 0 < m ==> MultiplesVanish(a, b, m)
  {
    forall a: int, b: int, m: int | 0 < m
      ensures MultiplesVanish(a, b, m)
    {
      LemmaModMultiplesVanish(a, b, m);
    }
  }

  /* proves equivalent forms of modulus subtraction */
  lemma LemmaModSubtraction(x: nat, s: nat, d: nat)
    requires 0 < d
    requires 0 <= s <= x % d
    ensures x % d - s % d == (x - s) % d
  {
    LemmaModAuto(d);
  }

  lemma LemmaModSubtractionAuto()
    ensures forall x: nat, s: nat, d: nat {:trigger (x - s) % d}
              :: 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d
  {
    forall x: nat, s: nat, d: nat | 0 < d && 0 <= s <= x % d
      ensures x % d - s % d == (x - s) % d
    {
      LemmaModSubtraction(x, s, d);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to addition (read "ensures") */
  lemma LemmaAddModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) + (y % m)) % m == (x + y) % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaAddModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m}
              :: 0 < m ==> ((x % m) + (y % m)) % m == (x + y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures ((x % m) + (y % m)) % m == (x + y) % m
    {
      LemmaAddModNoop(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to addition (read "ensures") */
  lemma LemmaAddModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + (y % m)) % m == (x + y) % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaAddModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m}
              :: 0 < m ==> (x + (y % m)) % m == (x + y) % m
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall x: int, y: int, m: int {:trigger x + y % m} | 0 < m
      ensures (x + (y % m)) % m == (x + y) % m
    {
      LemmaAddModNoopRight(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures") */
  lemma LemmaSubModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) - (y % m)) % m == (x - y) % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaSubModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m}
              :: 0 < m ==> ((x % m) - (y % m)) % m == (x - y) % m
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall x: int, y: int, m: int {:trigger x % m - y % m} | 0 < m
      ensures ((x % m) - (y % m)) % m == (x - y) % m
    {
      LemmaSubModNoop(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures") */
  lemma LemmaSubModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - (y % m)) % m == (x - y) % m
  {
    LemmaModAuto(m);
  }

  lemma LemmaSubModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m}
              :: 0 < m ==> (x - (y % m)) % m == (x - y) % m
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall x: int, y: int, m: int {:trigger x - y % m} | 0 < m
      ensures (x - (y % m)) % m == (x - y) % m
    {
      LemmaSubModNoopRight(x, y, m);
    }
  }

  /* proves equivalent forms of modulus addition */
  lemma LemmaModAdds(a: int, b: int, d: int)
    requires 0 < d
    ensures a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)
    ensures (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
  {
    LemmaMulAuto();
    LemmaDivAuto(d);
  }

  lemma LemmaModAddsAuto()
    ensures forall a: int, b: int, d: int {:trigger (a + b) % d}
              :: 0 < d ==> && a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)
                           && ((a % d + b % d) < d ==> a % d + b % d == (a + b) % d)
  {
    forall a: int, b: int, d: int | 0 < d
      ensures && a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)
              && ((a % d + b % d) < d ==> a % d + b % d == (a + b) % d)
    {
      LemmaModAdds(a, b, d);
    }
  }

  @IsolateAssertions
  lemma LemmaModNegNeg(x: int, d: int)
    requires 0 < d
    ensures x % d == (x * (1 - d)) % d
  {
    assert (x - x * d) % d == x % d
    by {
      LemmaModAuto(d);
      var f := i => (x - i * d) % d == x % d;
      assert  MulAuto() ==> && f(0)
                            && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1))
                            && (forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1));
      LemmaMulInductionAuto(x, f);
    }
    LemmaMulAuto();
  }

  /* proves the validity of the quotient and remainder */
  @ResourceLimit("2200000")
  @TimeLimitMultiplier(10)
  lemma LemmaFundamentalDivModConverse(x: int, d: int, q: int, r: int)
    requires d != 0
    requires 0 <= r < d
    requires x == q * d + r
    ensures q == x / d
    ensures r == x % d
  {
    LemmaDivAuto(d);
    LemmaMulInductionAuto(q, u => u == (u * d + r) / d);
    LemmaMulInductionAuto(q, u => r == (u * d + r) % d);
  }

  @TimeLimitMultiplier(5)
  lemma LemmaFundamentalDivModConverseAuto()
    ensures forall x: int, d: int, q: int, r: int {:trigger q * d + r, x % d}
              :: d != 0 && 0 <= r < d && x == q * d + r ==> q == x / d && r == x % d
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall x: int, d: int, q: int, r: int {:trigger x / d, q * d, r < d} {:trigger x / d, q * d, 0 <= r}
      | d != 0 && 0 <= r < d && x == q * d + r
      ensures q == x / d && r == x % d
    {
      LemmaFundamentalDivModConverse(x, d, q, r);
    }
  }


  /* the remainder of any natural number x divided by a positive integer m is always less than m */
  lemma LemmaModPosBound(x: int, m: int)
    decreases x
    requires 0 <= x
    requires 0 < m
    ensures  0 <= x % m < m
  {
    LemmaModAuto(m);
  }

  lemma LemmaModPosBoundAuto()
    ensures forall x: int, m: int {:trigger x % m} :: 0 <= x && 0 < m ==> 0 <= x % m < m
  {
    forall x: int, m: int | 0 <= x && 0 < m
      ensures 0 <= x % m < m
    {
      LemmaModPosBound(x, m);
    }
  }

  lemma LemmaMulModNoopLeft(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * y % m == x * y % m
  {
    LemmaModAuto(m);
    LemmaMulInductionAuto(y, u => (x % m) * u % m == x * u % m);
  }

  lemma LemmaMulModNoopLeftAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> (x % m) * y % m == x * y % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x % m) * y % m == x * y % m
    {
      LemmaMulModNoopLeft(x, y, m);
    }
  }

  lemma LemmaMulModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures x * (y % m) % m == (x * y) % m
  {
    LemmaModAuto(m);
    LemmaMulInductionAuto(x, u => u * (y % m) % m == (u * y) % m);
  }

  lemma LemmaMulModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m}
              :: 0 < m ==> x * (y % m) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures x * (y % m) % m == (x * y) % m
    {
      LemmaMulModNoopRight(x, y, m);
    }
  }

  /* combines previous no-op mod lemmas into a general, overarching lemma */
  lemma LemmaMulModNoopGeneral(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) * y      ) % m == (x * y) % m
    ensures ( x      * (y % m)) % m == (x * y) % m
    ensures ((x % m) * (y % m)) % m == (x * y) % m
  {
    LemmaModPropertiesAuto();
    LemmaMulModNoopLeft(x, y, m);
    LemmaMulModNoopRight(x, y, m);
    LemmaMulModNoopRight(x % m, y, m);
  }

  lemma LemmaMulModNoopGeneralAuto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m}
              :: 0 < m ==> ((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures ((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == (x * y) % m
    {
      LemmaMulModNoopGeneral(x, y, m);
    }
  }

  lemma LemmaMulModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * (y % m) % m == (x * y) % m
  {
    LemmaMulModNoopGeneral(x, y, m);
  }

  lemma LemmaMulModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m}
              :: 0 < m ==> (x % m) * (y % m) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x % m) * (y % m) % m == (x * y) % m
    {
      LemmaMulModNoop(x, y, m);
    }
  }

  /* proves modulus equivalence in two forms */
  lemma LemmaModEquivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
  {
    LemmaModAuto(m);
  }

  lemma LemmaModEquivalenceAuto()
    ensures forall x: int, y: int, m: int {:trigger  x % m , y % m}
              :: 0 < m && x % m == y % m <==> 0 < m && (x - y) % m == 0
  {
    forall x: int, y: int, m: int | 0 < m
      ensures x % m == y % m <==> 0 < m && (x - y) % m == 0
    {
      LemmaModEquivalence(x, y, m);
    }
  }

  /* true if x%n and y%n are equal */
  ghost predicate IsModEquivalent(x: int, y: int, m: int)
    requires m > 0
    ensures x % m == y % m <==> (x - y) % m == 0
  {
    LemmaModEquivalence(x, y, m);
    (x - y) % m == 0 // same as x % n == y % n, but easier to do induction on x - y than x and y separately
  }

  /* if x % m == y % m, then (x * z) % m == (y * z) % m. */
  lemma LemmaModMulEquivalent(x: int, y: int, z: int, m: int)
    requires m > 0
    requires IsModEquivalent(x, y, m)
    ensures IsModEquivalent(x * z, y * z, m)
  {
    LemmaMulModNoopLeft(x, z, m);
    LemmaMulModNoopLeft(y, z, m);
  }

  lemma LemmaModMulEquivalentAuto()
    ensures forall x: int, y: int, z: int, m: int
              {:trigger IsModEquivalent(x * z, y * z, m)}
              :: m > 0 && IsModEquivalent(x, y, m) ==> IsModEquivalent(x * z, y * z, m)
  {
    forall x: int, y: int, z: int, m: int | m > 0 && IsModEquivalent(x, y, m)
      ensures IsModEquivalent(x * z, y * z, m)
    {
      LemmaModMulEquivalent(x, y, z, m);
    }
  }

  /* the remainder can increase with a larger divisor */
  lemma LemmaModOrdering(x: int, k: int, d: int)
    requires 1 < d
    requires 0 < k
    ensures 0 < d * k
    ensures x % d <= x % (d * k)
  {
    LemmaMulStrictlyIncreases(d,k);
    calc {
      x % d + d * (x / d);
      { LemmaFundamentalDivMod(x, d); }
      x;
      { LemmaFundamentalDivMod(x, d * k); }
      x % (d * k) + (d * k) * (x / (d * k));
      { LemmaMulIsAssociativeAuto(); }
      x % (d * k) + d * (k * (x / (d * k)));
    }
    calc {
      x % d;
       { LemmaModPropertiesAuto(); }
      (x % d) % d;
       { LemmaModMultiplesVanish(x / d  - k * (x / (d * k)), x % d, d); }
      (x % d + d * (x / d  - k * (x / (d * k)))) % d;
       { LemmaMulIsDistributiveSubAuto(); }
      (x % d + d * (x / d) - d * (k * (x / (d * k)))) % d;
      (x % (d * k)) % d;
    <= { LemmaModPropertiesAuto();
         LemmaModDecreases(x % (d * k), d); }
      x % (d * k);
    }
  }

  lemma LemmaModOrderingAuto()
    ensures forall k: int, d: int {:trigger d * k}
              :: 1 < d && 0 < k ==> 0 < d * k
    ensures forall x: int, k: int, d: int {:trigger x % (d * k)}
              :: 1 < d && 0 < k ==> x % d <= x % (d * k)
  {
    forall k: int, d: int {:trigger d * k} | (1 < d && 0 < k)
      ensures 1 < d && 0 < k ==> 0 < d * k
    {
      LemmaMulStrictlyIncreases(d, k);
    }
    forall x: int, k: int, d: int {:trigger x % (d * k)} | (1 < d && 0 < k)
      ensures (1 < d && 0 < k) ==> (x % d <= x % (d * k))
    {
      LemmaModOrdering(x, k, d);
    }
  }

  lemma LemmaModMod(x: int, a: int, b: int)
    requires 0 < a
    requires 0 < b
    ensures 0 < a * b
    ensures (x % (a * b)) % a == x % a
  {
    LemmaMulStrictlyPositiveAuto();
    calc {
      x;
      { LemmaFundamentalDivMod(x, a * b); }
      (a * b) * (x / (a * b)) + x % (a * b);
      { LemmaMulIsAssociativeAuto(); }
      a * (b * (x / (a * b))) + x % (a * b);
      { LemmaFundamentalDivMod(x % (a * b), a); }
      a * (b * (x / (a * b))) + a * (x % (a * b) / a) + (x % (a * b)) % a;
      { LemmaMulIsDistributiveAuto(); }
      a * (b * (x / (a * b)) + x % (a * b) / a) + (x % (a * b)) % a;
    }
    LemmaModPropertiesAuto();
    LemmaMulIsCommutativeAuto();
    LemmaFundamentalDivModConverse(x, a, b * (x / (a * b)) + x % (a * b) / a, (x % (a * b)) % a);
  }

  lemma LemmaModModAuto()
    ensures forall a: int, b: int {:trigger a * b}
              :: 0 < a && 0 < b ==> 0 < a * b
    ensures forall x: int, a: int, b: int {:trigger (x % (a * b)) % a, x % a}
              :: 0 < a && 0 < b ==> (x % (a * b)) % a == x % a
  {
    forall a: int, b: int {:trigger a * b} | 0 < a && 0 < b
      ensures 0 < a * b
    {
      LemmaMulStrictlyPositiveAuto();
    }
    forall x: int, a: int, b: int | 0 < a && 0 < b
      ensures (x % (a * b)) % a == x % a
    {
      LemmaModMod(x, a, b);
    }
  }

  lemma LemmaPartBound2(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures (x % y) % (y * z) < y
  {
    LemmaMulStrictlyPositiveAuto();
    LemmaModPropertiesAuto();
    assert x % y < y;
    LemmaMulIncreasesAuto();
    LemmaMulIsCommutativeAuto();
    assert y <= y * z;
    assert 0 <= x % y < y * z;
    LemmaModPropertiesAuto();
    LemmaSmallMod(x % y, y * z);
    assert (x % y) % (y * z) == x % y;
  }

  lemma LemmaPartBound2Auto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % y}
              :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && (x % y) % (y * z) < y
  {
    // https://github.com/dafny-lang/dafny/issues/4771
    forall x: int, y: int, z: int {:trigger y * z, 0 <= x} {:trigger 0 < z, 0 < y, 0 <= x} | 0 <= x && 0 < y && 0 < z
      ensures y * z > 0 && (x % y) % (y * z) < y
    {
      LemmaPartBound2(x, y, z);
    }
  }

  /* ensures the validity of an expanded form of the modulus operation,
   as expressed in the pre and post conditions */
  lemma LemmaModBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % (y * z) == y * ((x / y) % z) + x % y
  {
    LemmaMulStrictlyPositiveAuto();
    LemmaDivPosIsPos(x, y);
    assert 0 <= x / y;

    calc {
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
    <=    { LemmaPartBound1(x, y, z); }
      y * (z - 1) + (x % y) % (y * z);
    <    { LemmaPartBound2(x, y, z); }
      y * (z - 1) + y;
          { LemmaMulBasicsAuto(); }
      y * (z - 1) + y * 1;
          { LemmaMulIsDistributiveAuto(); }
      y * (z - 1 + 1);
      y * z;
    }

    calc {
      x % (y * z);
      { LemmaFundamentalDivMod(x, y); }
      (y * (x / y) + x%  y) % (y * z);
      {
        LemmaModPropertiesAuto();
        assert 0 <= x % y;
        LemmaMulNonnegative(y, x / y);
        assert (y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z;
        LemmaModAdds(y * (x / y), x % y, y * z);
      }
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
      {
        LemmaModPropertiesAuto();
        LemmaMulIncreases(z, y);
        LemmaMulIsCommutativeAuto();
        assert x % y < y <= y * z;
        LemmaSmallMod(x % y, y * z);
        assert (x % y) % (y * z) == x % y;
      }
      (y * (x / y)) % (y * z) + x % y;
      { LemmaTruncateMiddle(x / y, y, z); }
      y * ((x / y) % z) + x % y;
    }
  }

  lemma LemmaModBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger x % (y * z)}
              :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && x % (y * z) == y * ((x / y) % z) + x % y
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < y && 0 < z
      ensures y * z > 0 && x % (y * z) == y * ((x / y) % z) + x % y
    {
      LemmaModBreakdown(x, y, z);
    }
  }

}

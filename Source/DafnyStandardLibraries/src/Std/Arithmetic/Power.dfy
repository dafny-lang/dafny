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
module Std.Arithmetic.Power {
  import opened DivMod
  import opened GeneralInternals
  import opened Mul
  import opened MulInternals

  function Pow(b: int, e: nat): int
    decreases e
  {
    if e == 0 then
      1
    else
      b * Pow(b, e - 1)
  }

  /* A number raised to the power of 0 equals 1. */
  lemma LemmaPow0(b: int)
    ensures Pow(b, 0) == 1
  {
  }

  lemma LemmaPow0Auto()
    ensures forall b: nat {:trigger Pow(b, 0)} :: Pow(b, 0) == 1
  {
    forall b: nat {:trigger Pow(b, 0)}
      ensures Pow(b, 0) == 1
    {
      LemmaPow0(b);
    }
  }

  /* A number raised to the power of 1 equals the number itself. */
  lemma LemmaPow1(b: int)
    ensures Pow(b, 1) == b
  {
    calc {
      Pow(b, 1);
      {  }
      b * Pow(b, 0);
      { LemmaPow0(b); }
      b * 1;
      { LemmaMulBasicsAuto(); }
      b;
    }
  }

  lemma LemmaPow1Auto()
    ensures forall b: nat {:trigger Pow(b, 1)} :: Pow(b, 1) == b
  {
    forall b: nat {:trigger Pow(b, 1)}
      ensures Pow(b, 1) == b
    {
      LemmaPow1(b);
    }
  }

  /* 0 raised to a positive power equals 0. */
  lemma Lemma0Pow(e: nat)
    requires e > 0
    ensures Pow(0, e) == 0
  {
    LemmaMulBasicsAuto();
    if e != 1 {
      Lemma0Pow(e - 1);
    }
  }

  lemma Lemma0PowAuto()
    ensures forall e: nat {:trigger Pow(0, e)} :: e > 0 ==> Pow(0, e) == 0
  {
    forall e: nat {:trigger Pow(0, e)} | e > 0
      ensures Pow(0, e) == 0
    {
      Lemma0Pow(e);
    }
  }

  /* 1 raised to any power equals 1. */
  lemma Lemma1Pow(e: nat)
    ensures Pow(1, e) == 1
  {
    LemmaMulBasicsAuto();
    if e != 0 {
      Lemma1Pow(e - 1);
    }
  }

  lemma Lemma1PowAuto()
    ensures forall e: nat {:trigger Pow(1, e)} :: Pow(1, e) == 1
  {
    forall e: nat {:trigger Pow(1, e)}
      ensures Pow(1, e) == 1
    {
      Lemma1Pow(e);
    }
  }

  /* Squaring a number is equal to raising it to the power of 2. */
  lemma LemmaSquareIsPow2(x: nat)
    ensures Pow(x, 2) == x * x
  {
  }

  lemma LemmaSquareIsPow2Auto()
    ensures forall x: nat {:trigger Pow(x, 2)} :: Pow(x, 2) == x * x
  {
    forall x: nat {:trigger Pow(x, 2)}
      ensures Pow(x, 2) == x * x
    {}
  }

  /* A positive number raised to any power is positive. */
  lemma LemmaPowPositive(b: int, e: nat)
    requires b > 0
    ensures 0 < Pow(b, e)
  {
    LemmaMulIncreasesAuto();
    LemmaPow0Auto(); // Base case
    // Distributes power i + 1 in first inductive step
    LemmaMulInductionAuto(e, u => 0 <= u ==> 0 < Pow(b, u));
  }

  lemma LemmaPowPositiveAuto()
    ensures forall b: int, e: nat {:trigger Pow(b, e)}
              :: b > 0 ==> 0 < Pow(b, e)
  {
    forall b: int, e: nat {:trigger Pow(b, e)} | b > 0
      ensures 0 < Pow(b, e)
    {
      LemmaPowPositive(b, e);
    }
  }

  /* Add exponents when multiplying powers with the same base. */
  lemma LemmaPowAdds(b: int, e1: nat, e2: nat)
    decreases e1
    ensures Pow(b, e1 + e2) == Pow(b, e1) * Pow(b, e2)
  {
    if e1 == 0 {
      calc {
        Pow(b, e1) * Pow(b, e2);
        { LemmaPow0(b); }
        1 * Pow(b, e2);
        { LemmaMulBasicsAuto(); }
        Pow(b, 0 + e2);
      }
    }
    else {
      calc {
        Pow(b, e1) * Pow(b, e2);
        {  }
        (b * Pow(b, e1 - 1)) * Pow(b, e2);
        { LemmaMulIsAssociativeAuto(); }
        b * (Pow(b, e1 - 1) * Pow(b, e2));
        { LemmaPowAdds(b, e1 - 1, e2); }
        b * Pow(b, e1 - 1 + e2);
        {  }
        Pow(b, e1 + e2);
      }
    }
  }

  lemma LemmaPowAddsAuto()
    ensures forall b: int, e1: nat, e2: nat {:trigger Pow(b, e1 + e2)}
              :: Pow(b, e1 + e2) == Pow(b, e1) * Pow(b, e2)
  {
    forall b: int, e1: nat, e2: nat {:trigger Pow(b, e1 + e2)}
      ensures Pow(b, e1 + e2) == Pow(b, e1) * Pow(b, e2)
    {
      LemmaPowAdds(b, e1, e2);
    }
  }

  lemma LemmaPowSubAddCancel(b: int, e1: nat, e2: nat)
    decreases e1
    requires e1 >= e2
    ensures Pow(b, e1 - e2) * Pow(b, e2) == Pow(b, e1)
  {
    LemmaPowAdds(b, e1 - e2, e2);
  }

  lemma LemmaPowSubAddCancelAuto()
    ensures forall b: int, e1: nat, e2: nat {:trigger Pow(b, e1 - e2)} | e1 >= e2
              :: Pow(b, e1 - e2) * Pow(b, e2) == Pow(b, e1)
  {
    forall b: int, e1: nat, e2: nat | e1 >= e2
    {
      LemmaPowSubAddCancel(b, e1, e2);
    }
  }

  /* Subtract exponents when dividing powers. */
  lemma LemmaPowSubtracts(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures Pow(b, e1) > 0
    ensures Pow(b, e2 - e1) == Pow(b, e2) / Pow(b, e1) > 0
  {
    LemmaPowPositiveAuto();
    calc {
      Pow(b, e2) / Pow(b, e1);
      { LemmaPowSubAddCancel(b, e2, e1); }
      Pow(b, e2 - e1) * Pow(b, e1) / Pow(b, e1);
      { LemmaDivByMultiple(Pow(b, e2 - e1), Pow(b, e1)); }
      Pow(b, e2 - e1);
    }
  }

  lemma LemmaPowSubtractsAuto()
    ensures forall b: nat, e1: nat :: b > 0 ==> Pow(b, e1) > 0
    ensures forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e2 - e1)}
              :: b > 0 && e1 <= e2 ==>
                   Pow(b, e2 - e1) == Pow(b, e2) / Pow(b, e1) > 0
  {
    LemmaPowPositiveAuto();
    forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e2 - e1)}
      | b > 0 && e1 <= e2
      ensures Pow(b, e2 - e1) == Pow(b, e2) / Pow(b, e1) > 0
    {
      LemmaPowSubtracts(b, e1, e2);
    }
  }

  /* Multiply exponents when finding the power of a power. */
  lemma LemmaPowMultiplies(a: int, b: nat, c: nat)
    decreases c
    ensures 0 <= b * c
    ensures Pow(Pow(a, b), c) == Pow(a, b * c)
  {
    LemmaMulNonnegative(b, c);
    if c == 0 {
      LemmaMulBasicsAuto();
      calc {
        Pow(a, b * c);
        { LemmaPow0(a); }
        1;
        { LemmaPow0(Pow(a, b)); }
        Pow(Pow(a, b), c);
      }
    }
    else {
      calc {
        b * c - b;
        { LemmaMulBasicsAuto(); }
        b * c - b * 1;
        { LemmaMulIsDistributiveAuto(); }
        b * (c - 1);
      }
      LemmaMulNonnegative(b, c - 1);
      assert 0 <= b * c - b;

      calc {
        Pow(a, b * c);
        Pow(a, b + b * c - b);
        { LemmaPowAdds(a, b, b * c - b); }
        Pow(a, b) * Pow(a, b * c - b);
        Pow(a, b) * Pow(a, b * (c - 1));
        { LemmaPowMultiplies(a, b, c - 1); }
        Pow(a, b) * Pow(Pow(a, b), c - 1);
        {  }
        Pow(Pow(a, b), c);
      }
    }
  }

  lemma LemmaPowMultipliesAuto()
    ensures forall b: nat, c: nat {:trigger b * c} :: 0 <= b * c
    ensures forall a: int, b: nat, c: nat {:trigger Pow(a, b * c)}
              :: Pow(Pow(a, b), c) == Pow(a, b * c)
  {
    LemmaMulNonnegativeAuto();
    forall a: int, b: nat, c: nat {:trigger Pow(a, b * c)}
      ensures Pow(Pow(a, b), c) == Pow(a, b * c)
    {
      LemmaPowMultiplies(a, b, c);
    }
  }

  /* Distribute the power to factors of a product. */
  lemma LemmaPowDistributes(a: int, b: int, e: nat)
    decreases e
    ensures Pow(a * b, e) == Pow(a, e) * Pow(b, e)
  {
    LemmaMulBasicsAuto();
    if e > 0 {
      calc {
        Pow(a * b, e);
        (a * b) * Pow(a * b, e - 1);
        { LemmaPowDistributes(a, b, e - 1); }
        (a * b) * (Pow(a, e - 1) * Pow(b, e - 1));
        { LemmaMulIsAssociativeAuto(); LemmaMulIsCommutativeAuto(); }
        (a * Pow(a, e - 1)) * (b * Pow(b, e - 1));
        Pow(a, e) * Pow(b, e);
      }
    }
  }

  lemma LemmaPowDistributesAuto()
    ensures forall a: int, b: int, e: nat {:trigger Pow(a * b, e)}
              :: Pow(a * b, e) == Pow(a, e) * Pow(b, e)
  {
    forall a: int, b: int, e: nat {:trigger Pow(a * b, e)}
      ensures Pow(a * b, e) == Pow(a, e) * Pow(b, e)
    {
      LemmaPowDistributes(a, b, e);
    }
  }

  /* Group properties of powers. */
  lemma LemmaPowAuto()
    ensures forall x: int {:trigger Pow(x, 0)} :: Pow(x, 0) == 1
    ensures forall x: int {:trigger Pow(x, 1)} :: Pow(x, 1) == x
    ensures forall x: int, y: int {:trigger Pow(x, y)} :: y == 0 ==> Pow(x, y) == 1
    ensures forall x: int, y: int {:trigger Pow(x, y)} :: y == 1 ==> Pow(x, y) == x
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y
    ensures forall x: int, y: nat, z: nat {:trigger Pow(x, y + z)} :: Pow(x, y + z) == Pow(x, y) * Pow(x, z)
    ensures forall x: int, y: nat, z: nat {:trigger Pow(x, y - z)} :: y >= z ==> Pow(x, y - z) * Pow(x, z) == Pow(x, y)
    ensures forall x: int, y: int, z: nat {:trigger Pow(x * y, z)} :: Pow(x * y, z) == Pow(x, z) * Pow(y, z)
  {

    LemmaPow0Auto();
    LemmaPow1Auto();

    LemmaPowDistributesAuto();
    LemmaPowAddsAuto();
    LemmaPowSubAddCancelAuto();

    LemmaMulAuto();
    LemmaMulIncreasesAuto();
    LemmaMulStrictlyIncreasesAuto();
  }

  /* A positive number raised to a power strictly increases as the power
  strictly increases. */
  lemma LemmaPowStrictlyIncreases(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires e1 < e2
    ensures Pow(b, e1) < Pow(b, e2)
  {
    LemmaPowAuto();
    var f := e => 0 < e ==> Pow(b, e1) < Pow(b, e1 + e);
    forall i {:trigger IsLe(0, i)} | IsLe(0, i) && f(i)
      ensures f(i + 1)
    {
      assert 0 < i ==> Pow(b, e1) < Pow(b, e1 + i);
      calc {
         Pow(b, e1 + i);
      <= { LemmaPowPositive(b, e1 + i);
           LemmaMulLeftInequality(Pow(b, e1 + i), 1, b); }
         Pow(b, e1 + i) * b;
      == { LemmaPow1(b); }
         Pow(b, e1 + i) * Pow(b, 1);
      == { LemmaPowAdds(b, e1 + i, 1); }
         Pow(b, e1 + i + 1);
      == calc {
           e1 + i + 1;
           e1 + (i + 1);
         }
         Pow(b, e1 + (i + 1));
      }
      assert f(i+1);
    }
    LemmaMulInductionAuto(e2 - e1, f);
    assert Pow(b, e1) < Pow(b, e1 + (e2 - e1)) == Pow(b, e2) by {
      assert 0 < e2 - e1;
    }
  }

  lemma LemmaPowStrictlyIncreasesAuto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1),
              Pow(b, e2)} :: (1 < b && e1 < e2) ==> Pow(b, e1) < Pow(b, e2)
  {
    forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1), Pow(b, e2)}
      | 1 < b && e1 < e2
      ensures Pow(b, e1) < Pow(b, e2)
    {
      LemmaPowStrictlyIncreases(b, e1, e2);
    }
  }

  /* A positive number raised to a power increases as the power increases. */
  lemma LemmaPowIncreases(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures Pow(b, e1) <= Pow(b, e2)
  {
    var f := e => 0 <= e ==> Pow(b, e1) <= Pow(b, e1 + e);
    forall i | IsLe(0, i) && f(i)
      ensures f(i + 1)
    {
      calc {
        Pow(b, e1 + i);
      <= { LemmaPowPositive(b, e1 + i);
           LemmaMulLeftInequality(Pow(b, e1 + i), 1, b); }
        Pow(b, e1 + i) * b;
      == { LemmaPow1(b); }
        Pow(b, e1 + i) * Pow(b, 1);
      == { LemmaPowAdds(b, e1 + i, 1); }
        Pow(b, e1 + i + 1);
      }
    }
    LemmaMulInductionAuto(e2 - e1, f);
    assert Pow(b, e1) <= Pow(b, e1 + (e2 - e1)) by {
      assert 0 <= e2 - e1;
    }
  }

  lemma LemmaPowIncreasesAuto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1),
              Pow(b, e2)} :: (1 < b && e1 <= e2) ==> Pow(b, e1) <= Pow(b, e2)
  {
    forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1), Pow(b, e2)}
      | 1 < b && e1 <= e2
      ensures Pow(b, e1) <= Pow(b, e2)
    {
      LemmaPowIncreases(b, e1, e2);
    }
  }

  /* A power strictly increases as a positive number raised to the power
  strictly increases. */
  lemma LemmaPowStrictlyIncreasesConverse(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires Pow(b, e1) < Pow(b, e2)
    ensures e1 < e2
  {
    if e1 >= e2 {
      LemmaPowIncreases(b, e2, e1);
      assert false;
    }
  }

  lemma LemmaPowStrictlyIncreasesConverseAuto()
    ensures forall b: nat, e1: nat, e2: nat
              {:trigger Pow(b, e1), Pow(b, e2)}
              :: b > 0 && Pow(b, e1) < Pow(b, e2) ==> e1 < e2
  {
    forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1), Pow(b, e2)}
      | b > 0 && Pow(b, e1) < Pow(b, e2)
      ensures e1 < e2
    {
      LemmaPowStrictlyIncreasesConverse(b, e1, e2);
    }
  }

  /* A power increases as a positive number raised to the power increases. */
  lemma LemmaPowIncreasesConverse(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires Pow(b, e1) <= Pow(b, e2)
    ensures e1 <= e2
  {
    if e1 > e2 {
      LemmaPowStrictlyIncreases(b, e2, e1);
      assert false;
    }
  }

  lemma LemmaPowIncreasesConverseAuto()
    ensures forall b: nat, e1: nat, e2: nat
              {:trigger Pow(b, e1), Pow(b, e2)}
              :: 1 < b && Pow(b, e1) <= Pow(b, e2) ==> e1 <= e2
  {
    forall b: nat, e1: nat, e2: nat {:trigger Pow(b, e1), Pow(b, e2)}
      | 1 < b && Pow(b, e1) <= Pow(b, e2)
      ensures e1 <= e2
    {
      LemmaPowIncreasesConverse(b, e1, e2);
    }
  }

  /* (b^xy)^z = (b^x)^yz */
  lemma LemmaPullOutPows(b: nat, x: nat, y: nat, z: nat)
    requires b > 0
    ensures 0 <= x * y
    ensures 0 <= y * z
    ensures Pow(Pow(b, x * y), z) == Pow(Pow(b, x), y * z)
  {
    LemmaMulNonnegative(x, y);
    LemmaMulNonnegative(y, z);
    LemmaPowPositive(b, x);
    calc {
      Pow(Pow(b, x * y), z);
      { LemmaPowMultiplies(b, x, y); }
      Pow(Pow(Pow(b, x), y), z);
      { LemmaPowMultiplies(Pow(b, x), y, z); }
      Pow(Pow(b, x), y * z);
    }
  }

  lemma LemmaPullOutPowsAuto()
    ensures forall y: nat, z: nat {:trigger z * y} :: 0 <= z * y && 0 <= y * z
    ensures forall b: nat, x: nat, y: nat, z: nat
              {:trigger Pow(Pow(b, x * y), z)}
              :: b > 0 ==> Pow(Pow(b, x * y), z) == Pow(Pow(b, x), y * z)
  {
    LemmaMulNonnegativeAuto();
    forall b: nat, x: nat, y: nat, z: nat {:trigger Pow(Pow(b, x * y), z)}
      | b > 0 ensures Pow(Pow(b, x * y), z) == Pow(Pow(b, x), y * z)
    {
      LemmaPullOutPows(b, x, y, z);
    }
  }

  /* Inequality due to smaller numerator, same denominator. */
  lemma LemmaPowDivisionInequality(x: nat, b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e2 <= e1
    requires x < Pow(b, e1)
    ensures Pow(b, e2) > 0
    ensures x / Pow(b, e2) < Pow(b, e1 - e2)
  {
    LemmaPowPositiveAuto();
    if (x / Pow(b, e2) >= Pow(b, e1 - e2)) {
      assert x / Pow(b, e2) >= Pow(b, e1 - e2);

      assert x / Pow(b, e2) * Pow(b, e2) >= Pow(b, e1 - e2) * Pow(b, e2) by
      { LemmaMulInequality(Pow(b, e1 - e2), x / Pow(b, e2), Pow(b, e2)); }

      assert x - x % Pow(b, e2) >= Pow(b, e1 - e2) * Pow(b, e2) by
      { LemmaFundamentalDivMod(x, Pow(b, e2));
        LemmaMulIsCommutativeAuto(); }

      assert x - x % Pow(b, e2) >= Pow(b, e1) by
      { LemmaPowAdds(b, e1 - e2, e2); }

      assert x >= Pow(b, e1) by
      { LemmaModPropertiesAuto(); }

      //assert false;
    }
  }

  lemma LemmaPowDivisionInequalityAuto()
    ensures forall b: nat, e2: nat :: b > 0 ==> Pow(b, e2) > 0
    ensures forall x: nat, b: nat, e1: nat, e2: nat
              {:trigger x / Pow(b, e2), Pow(b, e1 - e2)}
              :: b > 0 && e2 <= e1 && x < Pow(b, e1) ==>
                   x / Pow(b, e2) < Pow(b, e1 - e2)
  {
    LemmaPowPositiveAuto();
    forall x: nat, b: nat, e1: nat, e2: nat
      {:trigger x / Pow(b, e2), Pow(b, e1 - e2)}
      | b > 0 && e2 <= e1 && x < Pow(b, e1)
      ensures x / Pow(b, e2) < Pow(b, e1 - e2)
    {
      LemmaPowDivisionInequality(x, b, e1, e2);
    }
  }

  /* b^e % b = 0 */
  lemma {:induction false} LemmaPowMod(b: nat, e: nat)
    requires b > 0 && e > 0
    ensures Pow(b, e) % b == 0
  {
    calc {
      Pow(b, e) % b;
      (b * Pow(b, e - 1)) % b;
      { LemmaMulIsCommutative(b, Pow(b, e - 1)); }
      (Pow(b, e - 1) * b) % b;
      {
        LemmaPowPositiveAuto();
        LemmaModMultiplesBasic(Pow(b, e-1) , b);
      }
      0;
    }
  }

  lemma LemmaPowModAuto()
    ensures forall b: nat, e: nat {:trigger Pow(b, e)}
              :: b > 0 && e > 0 ==> Pow(b, e) % b == 0
  {
    forall b: nat, e: nat {:trigger Pow(b, e)} | b > 0 && e > 0
      ensures Pow(b, e) % b == 0
    {
      LemmaPowMod(b, e);
    }
  }

  /* ((b % e)^e) % m = b^e % m */
  lemma LemmaPowModNoop(b: int, e: nat, m: int)
    decreases e
    requires m > 0
    ensures Pow(b % m, e) % m == Pow(b, e) % m
  {
    LemmaModPropertiesAuto();
    if e > 0 {
      calc {
        Pow(b % m, e) % m;
        ((b % m) * Pow(b % m, e - 1)) % m;
        { LemmaMulModNoopGeneral(b, Pow(b % m, e - 1), m); }
        ((b % m) * (Pow(b % m, e - 1) % m) % m) % m;
        { LemmaPowModNoop(b, e - 1, m); }
        ((b % m) * (Pow(b, e - 1) % m) % m) % m;
        { LemmaMulModNoopGeneral(b, Pow(b, e - 1), m); }
        (b * (Pow(b, e - 1)) % m) % m;
        (b * (Pow(b, e - 1))) % m;
        Pow(b, e) % m;
      }
    }
  }

  lemma LemmaPowModNoopAuto()
    ensures forall b: nat, e: nat, m: nat {:trigger Pow(b % m, e)}
              :: m > 0 ==> Pow(b % m, e) % m == Pow(b, e) % m
  {
    forall b: nat, e: nat, m: nat {:trigger Pow(b % m, e)}
      | m > 0 ensures Pow(b % m, e) % m == Pow(b, e) % m
    {
      LemmaPowModNoop(b, e, m);
    }
  }

}

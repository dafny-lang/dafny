@DisableNonlinearArithmetic
module Std.Arithmetic.Logarithm {
  import opened Mul
  import opened DivMod
  import opened Power

  function Log(base: nat, pow: nat): nat
    requires base > 1
    decreases pow
  {
    if pow < base then 0
    else
      LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto();
      1 + Log(base, pow / base)
  }

  lemma {:induction false} LemmaLog0(base: nat, pow: nat)
    requires base > 1
    requires pow < base
    ensures Log(base, pow) == 0
  {
  }

  lemma {:induction false} LemmaLogS(base: nat, pow: nat)
    requires base > 1
    requires pow >= base
    ensures pow / base >= 0
    ensures Log(base, pow) == 1 + Log(base, pow / base)
  {
    LemmaDivPosIsPosAuto();
  }

  lemma {:induction false} LemmaLogSAuto()
    ensures forall base: nat, pow: nat
              {:trigger Log(base, pow / base)}
              | && base > 1
                && pow >= base
              :: && pow / base >= 0
                 && Log(base, pow) == 1 + Log(base, pow / base)
  {
    forall base: nat, pow: nat | && base > 1 && pow >= base
      ensures && pow / base >= 0
              && Log(base, pow) == 1 + Log(base, pow / base)
    {
      LemmaLogS(base, pow);
    }
  }

  lemma {:induction false} LemmaLogIsOrdered(base: nat, pow: nat, pow': nat)
    requires base > 1
    requires pow <= pow'
    ensures Log(base, pow) <= Log(base, pow')
    decreases pow
  {
    if pow' < base {
      assert Log(base, pow) == 0 == Log(base, pow');
    } else if pow < base {
      assert Log(base, pow) == 0;
    } else {
      LemmaDivPosIsPosAuto(); LemmaDivDecreasesAuto(); LemmaDivIsOrderedAuto();
      LemmaLogIsOrdered(base, pow / base, pow' / base);
    }
  }

  lemma {:induction false} LemmaLogPow(base: nat, n: nat)
    requires base > 1
    ensures (LemmaPowPositive(base, n); Log(base, Pow(base, n)) == n)
  {
    if n == 0 {
    } else {
      LemmaPowPositive(base, n);
      calc {
        Log(base, Pow(base, n));
        {  }
        Log(base, base * Pow(base, n - 1));
        { LemmaPowPositive(base, n - 1);
          LemmaMulIncreases(Pow(base, n - 1), base);
          LemmaMulIsCommutative(Pow(base, n - 1), base);
          LemmaLogS(base, base * Pow(base, n - 1)); }
        1 + Log(base, (base * Pow(base, n - 1)) / base);
        { LemmaDivMultiplesVanish(Pow(base, n - 1), base); }
        1 + Log(base, Pow(base, n - 1));
        { LemmaLogPow(base, n - 1); }
        1 + (n - 1);
      }
    }
  }

  // TODO
  // lemma {:induction false} Pow_Log(base: nat, pow: nat)
  //   requires base > 1
  //   requires pow > 0
  //   ensures Pow(base, Log(base, pow)) <= pow < Pow(base, Log(base, pow) + 1)
}

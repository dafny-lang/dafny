module ArithmeticExamples {
  import opened DafnyStdLibs.Arithmetic.Logarithm
  import opened DafnyStdLibs.Arithmetic.Power
  import opened DafnyStdLibs.Arithmetic.Mul

  /* log_b(m * n) = log_b(m) + log_b(n) if m and n are also powers of b */
  lemma LogProductRule(b: nat, x: nat, y: nat)
    requires b > 1
    ensures (
      LemmaPowPositive(b, x);
      LemmaPowPositive(b, y);
      LemmaMulIncreases(Pow(b, x), Pow(b, y));
      Log(b, Pow(b, x) * Pow(b, y)) == Log(b, Pow(b, x)) + Log(b, Pow(b, y))
    )
  {
    LemmaPowAdds(b, x, y);
    LemmaLogPow(b, x + y);
    LemmaLogPow(b, x);
    LemmaLogPow(b, y);
  }
}
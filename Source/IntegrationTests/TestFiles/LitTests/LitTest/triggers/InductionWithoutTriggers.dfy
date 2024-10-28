// RUN: %testDafnyForEachResolver "%s" --expect-exit-code=4

ghost function Sum(n: nat, f: int -> int): int
{
  if n == 0 then 0 else f(n-1) + Sum(n-1, f)
}

lemma TestTriggerWithLambdaExpression(n: nat, f: int -> int, g: int -> int)
{
  // Once, trigger selection would crash on the following quantifier, which uses a LambdaExpr.
  assert forall n: nat, f: int -> int :: Sum(n, x => 500 + f(x)) == n + Sum(n, f); // error: this does not hold
}

// With an explicit :induction attribute, the induction hypothesis emitted lets the proof of the lemma go through.
// However, there is no good matching pattern for the induction hypothesis, so a warning is generated.
// For a manual proof of this lemma, see lemma ExchangeEta in hofs/SumSum.dfy.
lemma {:induction n} ExchangeEtaWithInductionAttribute(n: nat, f: int -> int, g: int -> int) // warning: no trigger
  requires forall i :: 0 <= i < n ==> f(i) == g(i)
  ensures Sum(n, x => f(x)) == Sum(n, x => g(x))
{
}

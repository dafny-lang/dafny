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


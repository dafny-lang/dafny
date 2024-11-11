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

// -------------------------------------------

type OpaqueType

// Recursive predicates. Note that the heuristics for finding candidate induction variables pay attention
// to whether or not the predicate is recursive.

predicate P(n: nat) {
  if n <= 0 then true else P(n - 1)
}

predicate Q(n: nat, b: bool) {
  if n <= 0 then true else Q(n - 1, !b)
}

// --------------------

lemma {:induction n, b} GivenListNoTrigger0(n: nat, o: OpaqueType, b: bool) // warning: no trigger
  requires 0 <= n < 100
  ensures P(if b then n else n)
{ // error: cannot prove postcondition
}

lemma {:induction n, b} GivenListNoTrigger1(n: nat, o: OpaqueType, b: bool) // warning: no trigger
  requires 0 <= n < 100
  ensures P(n)
{ // error: cannot prove postcondition
}

lemma {:induction n} GivenList(n: nat, o: OpaqueType, b: bool) // matching pattern for IH: P(n)
  requires 0 <= n < 100
  ensures P(n)
{
}

// --------------------
// Just {:inductionTrigger} says to automatically pick variables for the induction, but then omit trigger
lemma {:inductionTrigger} YesToIH(n: nat, o: OpaqueType, b: bool) // induction: n; warning: no trigger
  requires 0 <= n < 100
  ensures P(if b then n else n)
{
}
// {:induction} says to pick ALL parameters (of reasonable types) for the induction
lemma {:induction} YesToIH1(n: nat, o: OpaqueType, b: bool) // induction: n, b; warning: no trigger
  requires 0 <= n < 100
  ensures P(n)
{ // error: cannot prove postcondition
}

lemma {:induction} YesToIH2(n: nat, o: OpaqueType) // induction: n
  requires 0 <= n < 100
  ensures P(n)
{
}

// --------------------

lemma {:induction false} NoIH(n: nat, o: OpaqueType, b: bool)
  requires 0 <= n < 100
  ensures P(if b then n else n)
{ // error: cannot prove postcondition
}

lemma {:induction false} NoIHButManualProof(n: nat, o: OpaqueType, b: bool)
  requires 0 <= n < 100
  ensures P(if b then n else n)
{
  if n != 0 {
    NoIHButManualProof(n - 1, o, b);
  }
}

// --------------------

lemma AutomaticInduction(n: nat, o: OpaqueType, b: bool) // no induction, because no triggers (candidates: n)
  requires 0 <= n < 100
  ensures P(if b then n else n)
{ // error: cannot prove postcondition
}

lemma AutomaticInduction1(n: nat, o: OpaqueType, b: bool) // induction: n; trigger: P(n)
  requires 0 <= n < 100
  ensures P(n)
{
}

lemma AutomaticInduction2(n: nat, o: OpaqueType, b: bool) // induction: n, b; trigger: Q(n, b)
  requires 0 <= n < 100
  ensures Q(n, b)
{
}

lemma AutomaticInduction3(n: nat, o: OpaqueType, b: bool) // induction: n; trigger: Q(n, true)
  requires 0 <= n < 100
  ensures Q(n, true)
{
}

lemma AutomaticInduction4(n: nat, o: OpaqueType, b: bool) // no induction, because no triggers (candidates: n, b)
  requires 0 <= n < 100
  ensures P(n) && Q(n + 12, b)
{ // error (x2): cannot prove postconditions
}

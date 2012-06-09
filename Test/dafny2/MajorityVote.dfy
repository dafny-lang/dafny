method FindWinner<Candidate>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires 2 * Count(a, 0, |a|, K) > |a|;  // K has a (strict) majority of the votes
  ensures k == K;  // find K
{
  k := a[0];
  var n, c, s := 1, 1, 0;
  while (n < |a|)
    invariant 0 <= s <= n <= |a|;
    invariant 2 * Count(a, s, |a|, K) > |a| - s;  // K has majority among a[s..]
    invariant 2 * Count(a, s, n, k) > n - s;  // k has majority among a[s..n]
    invariant c == Count(a, s, n, k);
  {
    if (a[n] == k) {
      n, c := n + 1, c + 1;
    } else if (2 * c > n + 1 - s) {
      n := n + 1;
    } else {
      n := n + 1;
      // We have 2*Count(a, s, n, k) == n-s, and thus the following lemma
      // lets us conclude 2*Count(a, s, n, K) <= n-s.
      Lemma_Unique(a, s, n, K, k);
      // We also have 2*Count(a, s, |a|, K) > |a|-s, and the following lemma
      // tells us Count(a, s, |a|, K) == Count(a, s, n, K) + Count(a, n, |a|, K),
      // and thus we can conclude 2*Count(a, n, |a|, K) > |a|-n.
      Lemma_Split(a, s, n, |a|, K);
      k, n, c, s := a[n], n + 1, 1, n;
    }
  }
  Lemma_Unique(a, s, |a|, K, k);  // both k and K have a majority, so K == k
}

ghost method Lemma_Split<T>(a: seq<T>, s: int, t: int, u: int, x: T)
  requires 0 <= s <= t <= u <= |a|;
  ensures Count(a, s, t, x) + Count(a, t, u, x) == Count(a, s, u, x);
{
  /* The postcondition of this method is proved automatically via Dafny's
     induction tactic.  But if a manual proof had to be provided, it would
     look like this:
  if (s != t) {
    Lemma_Split(a, s, t-1, u, x);
  }
  */
}

ghost method Lemma_Unique<T>(a: seq<T>, s: int, t: int, x: T, y: T)
  requires 0 <= s <= t <= |a|;
  ensures x != y ==> Count(a, s, t, x) + Count(a, s, t, y) <= t - s;
{
  /* The postcondition of this method is proved automatically via Dafny's
     induction tactic.  But if a manual proof had to be provided, it would
     look like this:
  if (s != t) {
    Lemma_Unique(a, s, t-1, x, y);
  }
  */
}

function Count<T>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|;
{
  if s == t then 0 else
  Count(a, s, t-1, x) + if a[t-1] == x then 1 else 0
}

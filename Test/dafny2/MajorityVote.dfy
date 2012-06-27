// Rustan Leino, June 2012.
// This file verifies an algorithm, due to Boyer and Moore, that finds the majority choice
// among a sequence of votes, see http://www.cs.utexas.edu/~moore/best-ideas/mjrty/.
// Actually, this algorithm is a slight variation on theirs, but the general idea for why
// it is correct is the same.  In the Boyer and Moore algorithm, the loop counter is advanced
// by exactly 1 each iteration, which means that there may or may not be a "current leader".
// In my program below, I had instead written the loop invariant to say there is always a
// "current leader", which requires the loop index sometimes to skip a value.
//
// This file has two versions of the algorithm.  In the first version, the given sequence
// of votes is assumed to have a (strict) majority choice, meaning that strictly more than
// 50% of the votes are for one candidate.  It is convenient to have a name for the majority
// choice, in order to talk about it in specifications.  The easiest way to do this in
// Dafny is probably to introduce a ghost parameter with the given properties.  That's what
// the algorithm does, see parameter K.  The postcondition is thus to output the value of
// K, which is done in the non-ghost out-parameter k.
// The proof of the algorithm requires two lemmas.  These lemmas are proved automatically
// by Dafny's induction tactic.
//
// In the second version of the program, the main method does not assume there is a majority
// choice.  Rather, it eseentially uses the first algorithm and then checks if what it
// returns really is a majority choice.  To do this, the specification of the first algorithm
// needs to be changed slightly to accommodate the possibility that there is no majority
// choice.  That change in specification is also reflected in the loop invariant.  Moreover,
// the algorithm itself now needs to extra 'if' statements to see if the entire sequence
// has been searched through.  (This extra 'if' is essentially already handled by Boyer and
// Moore's algorithm, because it increments the loop index by 1 each iteration and therefore
// already has a special case for the case of running out of sequence elements without a
// current leader.)
// The calling harness, DetermineElection, somewhat existentially comes up with the majority
// choice, if there is such a choice, and then passes in that choice as the ghost parameter K
// to the main algorithm.  Neat, huh?

// Language comment:
// The "(==)" that sits after some type parameters in this program says that the actual
// type argument must support equality.

// Advanced remark:
// There is a subtle situation in the verification of DetermineElection.  Suppose the type
// parameter Candidate denotes some type whose instances depend on which object are
// allocated.  For example, if Candidate is some class type, then more candidates can come
// into being by object allocations (using "new").  What does the quantification of
// candidates "c" in the postcondition of DetermineElection now mean--all candidates that
// existed in the pre-state or (the possibly larger set of) all candidates that exist in the
// post-state?  (It means the latter.)  And if there does not exist a candidate in majority
// in the pre-state, could there be a (newly created) candidate in majority in the post-state?
// This will require some proof.  The simplest argument seems to be that even if more candidates
// are created during the course of DetermineElection, such candidates cannot possibly
// be in majority in the sequence "a", since "a" can only contain candidates that were already
// created in the pre-state.  This property is easily specified by adding a postcondition
// to the Count function.  Alternatively, one could have added the antecedent "c in a" or
// "old(allocated(c))" to the "forall c" quantification in the postcondition of DetermineElection.

function method Count<T(==)>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|;
  ensures Count(a, s, t, x) == 0 || x in a;
{
  if s == t then 0 else
  Count(a, s, t-1, x) + if a[t-1] == x then 1 else 0
}

// Here is the first version of the algorithm, the one that assumes there is a majority choice.

method FindWinner<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
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

// ------------------------------------------------------------------------------

// Here is the second version of the program, the one that also computes whether or not
// there is a majority choice.

method DetermineElection<Candidate(==)>(a: seq<Candidate>) returns (hasWinner: bool, cand: Candidate)
  ensures hasWinner ==> 2 * Count(a, 0, |a|, cand) > |a|;
  ensures !hasWinner ==> forall c :: 2 * Count(a, 0, |a|, c) <= |a|;
{
  ghost var b := exists c :: 2 * Count(a, 0, |a|, c) > |a|;
  ghost var w :| b ==> 2 * Count(a, 0, |a|, w) > |a|;
  cand := SearchForWinner(a, b, w);
  return 2 * Count(a, 0, |a|, cand) > |a|, cand;
}

// The difference between SearchForWinner for FindWinner above are the occurrences of the
// antecedent "hasWinner ==>" and the two checks for no-more-votes that may result in a "return"
// statement.

method SearchForWinner<Candidate(==)>(a: seq<Candidate>, ghost hasWinner: bool, ghost K: Candidate) returns (k: Candidate)
  requires hasWinner ==> 2 * Count(a, 0, |a|, K) > |a|;  // K has a (strict) majority of the votes
  ensures hasWinner ==> k == K;  // find K
{
  if (|a| == 0) { return; }
  k := a[0];
  var n, c, s := 1, 1, 0;
  while (n < |a|)
    invariant 0 <= s <= n <= |a|;
    invariant hasWinner ==> 2 * Count(a, s, |a|, K) > |a| - s;  // K has majority among a[s..]
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
      if (|a| == n) { return; }
      k, n, c, s := a[n], n + 1, 1, n;
    }
  }
  Lemma_Unique(a, s, |a|, K, k);  // both k and K have a majority, so K == k
}

// ------------------------------------------------------------------------------

// Here are two lemmas about Count that are used in the methods above.

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

// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

// About reading the proofs:
// Dafny proves the FindWinner algorithm from the given loop invariants and the two lemmas
// Lemma_Unique and Lemma_Split.  In showing this proof to some colleagues, they found they
// were not as quick as Dafny in constructing the proof from these ingredients.  For a human
// to understand the situation better, it helps to take smaller (and more) steps in the proof.
// At the end of this file, Nadia Polikarpova has written two versions of FindWinner that does
// that, using Dafny's support for calculational proofs.

function method Count<T(==)>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else
  Count(a, s, t-1, x) + if a[t-1] == x then 1 else 0
}

predicate HasMajority<T>(a: seq<T>, s: int, t: int, x: T)
  requires 0 <= s <= t <= |a|
{
  2 * Count(a, s, t, x) > t - s
}

// Here is the first version of the algorithm, the one that assumes there is a majority choice.

method FindWinner<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K) // K has a (strict) majority of the votes
  ensures k == K  // find K
{
  k := a[0];
  var n, c, s := 1, 1, 0;
  while n < |a|
    invariant 0 <= s <= n <= |a|
    invariant 2 * Count(a, s, |a|, K) > |a| - s  // K has majority among a[s..]
    invariant 2 * Count(a, s, n, k) > n - s  // k has majority among a[s..n]
    invariant c == Count(a, s, n, k)
  {
    if a[n] == k {
      n, c := n + 1, c + 1;
    } else if 2 * c > n + 1 - s {
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

datatype Result<Candidate> = NoWinner | Winner(cand: Candidate)

method DetermineElection<Candidate(==,0,!new)>(a: seq<Candidate>) returns (result: Result<Candidate>)
  ensures result.Winner? ==> 2 * Count(a, 0, |a|, result.cand) > |a|
  ensures result.NoWinner? ==> forall c :: 2 * Count(a, 0, |a|, c) <= |a|
{
  if |a| == 0 { return NoWinner; }
  ghost var b := exists c :: 2 * Count(a, 0, |a|, c) > |a|;
  ghost var w :| b ==> 2 * Count(a, 0, |a|, w) > |a|;
  var cand := SearchForWinner(a, b, w);
  return if 2 * Count(a, 0, |a|, cand) > |a| then Winner(cand) else NoWinner;
}

// The difference between SearchForWinner for FindWinner above are the occurrences of the
// antecedent "hasWinner ==>" and the two checks for no-more-votes that may result in a "return"
// statement.

method SearchForWinner<Candidate(==)>(a: seq<Candidate>, ghost hasWinner: bool, ghost K: Candidate) returns (k: Candidate)
  requires |a| != 0
  requires hasWinner ==> 2 * Count(a, 0, |a|, K) > |a|  // K has a (strict) majority of the votes
  ensures hasWinner ==> k == K  // find K
{
  k := a[0];
  var n, c, s := 1, 1, 0;
  while n < |a|
    invariant 0 <= s <= n <= |a|
    invariant hasWinner ==> 2 * Count(a, s, |a|, K) > |a| - s  // K has majority among a[s..]
    invariant 2 * Count(a, s, n, k) > n - s  // k has majority among a[s..n]
    invariant c == Count(a, s, n, k)
  {
    if a[n] == k {
      n, c := n + 1, c + 1;
    } else if 2 * c > n + 1 - s {
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
      if |a| == n { return; }
      k, n, c, s := a[n], n + 1, 1, n;
    }
  }
  Lemma_Unique(a, s, |a|, K, k);  // both k and K have a majority, so K == k
}

// ------------------------------------------------------------------------------

// Here are two lemmas about Count that are used in the methods above.

lemma Lemma_Split<T>(a: seq<T>, s: int, t: int, u: int, x: T)
  requires 0 <= s <= t <= u <= |a|
  ensures Count(a, s, t, x) + Count(a, t, u, x) == Count(a, s, u, x)
{
  /* The postcondition of this method is proved automatically via Dafny's
     induction tactic.  But if a manual proof had to be provided, it would
     look like this:
  if s != t {
    Lemma_Split(a, s, t-1, u, x);
  }
  */
}

lemma Lemma_Unique<T>(a: seq<T>, s: int, t: int, x: T, y: T)
  requires 0 <= s <= t <= |a|
  ensures x != y ==> Count(a, s, t, x) + Count(a, s, t, y) <= t - s
{
  /* The postcondition of this method is proved automatically via Dafny's
     induction tactic.  But if a manual proof had to be provided, it would
     look like this:
  if s != t {
    Lemma_Unique(a, s, t-1, x, y);
  }
  */
}

// ------------------------------------------------------------------------------

// This version uses more calculations with integer formulas
method FindWinner'<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K) // K has a (strict) majority of the votes
  ensures k == K  // find K
{
  k := a[0]; // Current candidate: the first element
  var lo, up, c := 0, 1, 1; // Window: [0..1], number of occurrences of k in the window: 1
  while up < |a|
    invariant 0 <= lo < up <= |a| // (0)
    invariant HasMajority(a, lo, |a|, K) // (1) K has majority among a[lo..]
    invariant HasMajority(a, lo, up, k) // (2) k has majority among a[lo..up] (in the current window)
    invariant c == Count(a, lo, up, k) // (3)
  {
    if a[up] == k {
      // One more occurrence of k
      up, c := up + 1, c + 1;
    } else if 2 * c > up + 1 - lo {
      // An occurrence of another value, but k still has the majority
      up := up + 1;
    } else {
      // An occurrence of another value and k just lost the majority.
      // Prove that k has exactly 50% in the future window a[lo..up + 1]:
      calc /* k has 50% among a[lo..up + 1] */ {
        true;
      ==  // negation of the previous branch condition;
        2 * c <= up + 1 - lo;
      ==  // loop invariant (3)
        2 * Count(a, lo, up, k) <= up + 1 - lo;
      == calc {
           true;
         ==  // loop invariant (2)
           HasMajority(a, lo, up, k);
         ==  // def. HasMajority
           2 * Count(a, lo, up, k) > up - lo;
         ==
           2 * Count(a, lo, up, k) >= up + 1 - lo;
         }
        2 * Count(a, lo, up, k) == up + 1 - lo;
      }
      up := up + 1;
      assert 2 * Count(a, lo, up, k) == up - lo; // k has exactly 50% in the current window a[lo..up]

      // We are going to start a new window a[up..up + 1] and choose a new candidate,
      // so invariants (2) and (3) will be easy to re-establish.
      // To re-establish (1) we have to prove that K has majority among a[up..], as up will become the new lo.
      // The main idea is that we had enough K's in a[lo..], and there cannot be too many in a[lo..up].
      calc /* K has majority among a[up..] */ {
        2 * Count(a, up, |a|, K);
      ==  { Lemma_Split(a, lo, up, |a|, K); }
        2 * Count(a, lo, |a|, K) - 2 * Count(a, lo, up, K);
      >  { assert HasMajority(a, lo, |a|, K); } // loop invariant (1)
        |a| - lo - 2 * Count(a, lo, up, K);
      >=  { if k == K {
              calc {
                2 * Count(a, lo, up, K);
              ==
                2 * Count(a, lo, up, k);
              ==  { assert 2 * Count(a, lo, up, k) == up - lo; } // k has 50% among a[lo..up]
                up - lo;
              }
            } else {
              calc {
                2 * Count(a, lo, up, K);
              <=  { Lemma_Unique(a, lo, up, k, K); }
                2 * ((up - lo) - Count(a, lo, up, k));
              ==  { assert 2 * Count(a, lo, up, k) == up - lo; } // k has 50% among a[lo..up]
                up - lo;
              }
            }
            assert 2 * Count(a, lo, up, K) <= up - lo;
          }
        |a| - lo - (up - lo);
      ==
        |a| - up;
      }
      assert HasMajority(a, up, |a|, K);

      k, lo, up, c := a[up], up, up + 1, 1;
      assert HasMajority(a, lo, |a|, K);
    }
  }
  Lemma_Unique(a, lo, |a|, K, k);  // both k and K have a majority among a[lo..], so K == k
}

// This version uses more calculations with boolean formulas
method FindWinner''<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K)  // K has a (strict) majority of the votes
  ensures k == K  // find K
{
  k := a[0]; // Current candidate: the first element
  var lo, up, c := 0, 1, 1; // Window: [0..1], number of occurrences of k in the window: 1
  while up < |a|
    invariant 0 <= lo < up <= |a| // (0)
    invariant HasMajority(a, lo, |a|, K) // (1) K has majority among a[lo..]
    invariant HasMajority(a, lo, up, k) // (2) k has majority among a[lo..up] (in the current window)
    invariant c == Count(a, lo, up, k) // (3)
  {
    if a[up] == k {
      // One more occurrence of k
      up, c := up + 1, c + 1;
    } else if 2 * c > up + 1 - lo {
      // An occurrence of another value, but k still has the majority
      up := up + 1;
    } else {
      // An occurrence of another value and k just lost the majority.
      // Prove that k has exactly 50% in the future window a[lo..up + 1]:
      calc /* k has 50% among a[lo..up + 1] */ {
        true;
      ==  // negation of the previous branch condition
        2 * c <= up + 1 - lo;
      ==  // loop invariant (3)
        2 * Count(a, lo, up, k) <= up + 1 - lo;
      ==  calc {
            true;
          ==  // loop invariant (2)
            HasMajority(a, lo, up, k);
          ==  // def. HasMajority
            2 * Count(a, lo, up, k) > up - lo;
          ==
            2 * Count(a, lo, up, k) >= up + 1 - lo;
          }
        2 * Count(a, lo, up, k) == up + 1 - lo;
      }
      up := up + 1;
      assert 2 * Count(a, lo, up, k) == up - lo; // k has exactly 50% in the current window a[lo..up]

      // We are going to start a new window a[up..up + 1] and choose a new candidate,
      // so invariants (2) and (3) will be easy to re-establish.
      // To re-establish (1) we have to prove that K has majority among a[up..], as up will become the new lo.
      // The main idea is that we had enough K's in a[lo..], and there cannot be too many in a[lo..up].
      calc /* K has majority among a[up..] */ {
        true;
      ==  // loop invariant (1)
        HasMajority(a, lo, |a|, K);
      ==
        2 * Count(a, lo, |a|, K) > |a| - lo;
      ==  { Lemma_Split(a, lo, up, |a|, K); }
        2 * Count(a, lo, up, K) + 2 * Count(a, up, |a|, K) > |a| - lo;
      ==>
        { if k == K {
            calc {
              2 * Count(a, lo, up, K);
            ==
              2 * Count(a, lo, up, k);
            ==  { assert 2 * Count(a, lo, up, k) == up - lo; } // k has 50% among a[lo..up]
              up - lo;
            }
          } else {
            calc {
              true;
            ==  { Lemma_Unique(a, lo, up, k, K); }
              Count(a, lo, up, K) + Count(a, lo, up, k) <= up - lo;
            ==
              2 * Count(a, lo, up, K) + 2 * Count(a, lo, up, k) <= 2 * (up - lo);
            ==  { assert 2 * Count(a, lo, up, k) == up - lo; } // k has 50% among a[lo..up]
              2 * Count(a, lo, up, K) <= up - lo;
            }
          }
          assert 2 * Count(a, lo, up, K) <= up - lo;
        }
        // subtract off Count(a, lo, up, K) from the LHS and subtract off the larger amount up - lo from the RHS
        2 * Count(a, up, |a|, K) > (|a| - lo) - (up - lo);
      ==
        2 * Count(a, up, |a|, K) > |a| - up;
      ==
        HasMajority(a, up, |a|, K);
      }
      k, lo, up, c := a[up], up, up + 1, 1;
      assert HasMajority(a, lo, |a|, K);
    }
  }
  Lemma_Unique(a, lo, |a|, K, k);  // both k and K have a majority among a[lo..], so K == k
}

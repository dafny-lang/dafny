// RUN: %exits-with 4 %dafny /compile:0 /induction:3 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class IntegerInduction {
  // This class considers different ways of proving, for any natural n:
  //   (SUM i in [0, n] :: i^3) == (SUM i in [0, n] :: i)^2

  // In terms of Dafny functions, the theorem to be proved is:
  //   SumOfCubes(n) == Gauss(n) * Gauss(n)

  function SumOfCubes(n: int): int
    requires 0 <= n;
  {
    if n == 0 then 0 else SumOfCubes(n-1) + n*n*n
  }

  function Gauss(n: int): int
    requires 0 <= n;
  {
    if n == 0 then 0 else Gauss(n-1) + n
  }

  // Here is one proof.  It uses a lemma, which is proved separately.

  lemma Theorem0(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == Gauss(n) * Gauss(n);
  {
    if (n != 0) {
      Theorem0(n-1);
      Lemma(n-1);
    }
  }

  lemma Lemma(n: int)
    requires 0 <= n;
    ensures 2 * Gauss(n) == n*(n+1);
  {
    if (n != 0) { Lemma(n-1); }
  }

  // Here is another proof.  It states the lemma as part of the theorem, and
  // thus proves the two together.

  lemma Theorem1(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == Gauss(n) * Gauss(n);
    ensures 2 * Gauss(n) == n*(n+1);
  {
    if (n != 0) {
      Theorem1(n-1);
    }
  }

  lemma DoItAllInOneGo()
    ensures (forall n {:split false} :: 0 <= n ==> // WISH reenable quantifier splitting here. This will only work once we generate induction hypotheses at the Dafny level.
                SumOfCubes(n) == Gauss(n) * Gauss(n) &&
                2 * Gauss(n) == n*(n+1));
  {
  }

  // The following two lemmas are the same as the previous two, but
  // here no body is given--and the proof still goes through (thanks to
  // Dafny's ghost-method induction tactic).

  lemma Lemma_Auto(n: int)
    requires 0 <= n;
    ensures 2 * Gauss(n) == n*(n+1);
  {
  }

  lemma Theorem1_Auto(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == Gauss(n) * Gauss(n);
    ensures 2 * Gauss(n) == n*(n+1);
  {
  }

  // Here is another proof.  It makes use of Dafny's induction heuristics to
  // prove the lemma.

  lemma Theorem2(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == Gauss(n) * Gauss(n);
  {
    if (n != 0) {
      Theorem2(n-1);

      assert (forall m :: 0 <= m ==> 2 * Gauss(m) == m*(m+1));
    }
  }

  lemma M(n: int)
    requires 0 <= n;
  {
    assume (forall k :: 0 <= k && k < n ==> 2 * Gauss(k) == k*(k+1));  // manually assume the induction hypothesis
    assert 2 * Gauss(n) == n*(n+1);
  }

  // Another way to prove the lemma is to supply a postcondition on the Gauss function

  lemma Theorem3(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == GaussWithPost(n) * GaussWithPost(n);
  {
    if (n != 0) {
      Theorem3(n-1);
    }
  }

  function GaussWithPost(n: int): int
    requires 0 <= n;
    ensures 2 * GaussWithPost(n) == n*(n+1);
  {
    if n == 0 then 0 else GaussWithPost(n-1) + n
  }

  // Finally, with the postcondition of GaussWithPost, one can prove the entire theorem by induction

  lemma Theorem4()
    ensures (forall n :: 0 <= n ==>
        SumOfCubes(n) == GaussWithPost(n) * GaussWithPost(n));
  {
    // look ma, no hints!
  }

  lemma Theorem5(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == GaussWithPost(n) * GaussWithPost(n);
  {
    // the postcondition is a simple consequence of these quantified versions of the theorem:
    if (*) {
      assert (forall m :: 0 <= m ==> SumOfCubes(m) == GaussWithPost(m) * GaussWithPost(m));
    } else {
      Theorem4();
    }
  }

  // The body of this function method gives a single quantifier, which leads to an efficient
  // way to check sortedness at run time.  However, an alternative, and ostensibly more general,
  // way to express sortedness is given in the function's postcondition.  The alternative
  // formulation may be easier to understand for a human and may also be more readily applicable
  // for the program verifier.  Dafny will show that postcondition holds, which ensures the
  // equivalence of the two formulations.
  // The proof of the postcondition requires induction.  It would have been nicer to state it
  // as one formula of the form "IsSorted(s) <==> ...", but then Dafny would never consider the
  // possibility of applying induction.  Instead, the "==>" and "<==" cases are given separately.
  // Proving the "<==" case is simple; it's the "==>" case that requires induction.
  // The example uses an attribute that requests induction on just "j".  However, the proof also
  // goes through by applying induction on both bound variables.
  function method IsSorted(s: seq<int>): bool //WISH remove autotriggers false
    ensures IsSorted(s) ==> (forall i,j {:induction j} {:autotriggers false} :: 0 <= i < j < |s| ==> s[i] <= s[j]);
    ensures (forall i,j :: 0 <= i && i < j && j < |s| ==> s[i] <= s[j]) ==> IsSorted(s);
  {
    (forall i {:nowarn} {:matchinglooprewrite false}:: 1 <= i && i < |s| ==> s[i-1] <= s[i])
  }
}

datatype Tree<T> = Leaf(T) | Branch(Tree<T>, Tree<T>)

class DatatypeInduction<T> {
  function LeafCount<T>(tree: Tree<T>): int
  {
    match tree
    case Leaf(t) => 1
    case Branch(left, right) => LeafCount(left) + LeafCount(right)
  }

  method Theorem0(tree: Tree<T>)
    ensures 1 <= LeafCount(tree);
  {
    assert (forall t: Tree<T> :: 1 <= LeafCount(t));
  }

  // see also Test/dafny0/DTypes.dfy for more variations of this example

  function OccurrenceCount<T>(tree: Tree<T>, x: T): int
  {
    match tree
    case Leaf(t) => if x == t then 1 else 0
    case Branch(left, right) => OccurrenceCount(left, x) + OccurrenceCount(right, x)
  }
  method RegressionTest(tree: Tree<T>)
    // the translation of the following line once crashed Dafny
    requires forall y :: 0 <= OccurrenceCount(tree, y);
  {
  }

}

// ----------------------- Induction and case splits -----------------
// This is a simple example where the induction hypothesis and the
// case splits are decoupled.

datatype D = Nothing | Something(D)

function FooD(n: nat, d: D): int
  ensures 10 <= FooD(n, d);
{
  match d
  case Nothing =>
    if n == 0 then 10 else FooD(n-1, D.Something(d))
  case Something(next) =>
    if n < 100 then n + 12 else FooD(n-13, next)
}

// ----------------------- Regression: remember to substitute "this" -----------------

class Node {
  ghost var Repr: set<object>
  var left: Node?
  var uu: nat

  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    (left != null ==>
      left in Repr && left.Repr <= Repr &&
      this !in left.Repr &&
      left.Valid()) &&
    ((left == null && uu == 0) || (left != null && uu != 0))
  }

  constructor ()
    ensures Valid() && fresh(Repr)
  {
    left := null;
    uu := 0;
    Repr := {this};
  }

  lemma InstanceAboutUU()
    requires Valid()
    ensures uu == 0 // regression: once upon a time, this used to go through
    decreases Repr
  {
    if left == null {
    } else { // error: postcondition violation
    }
  }
}

lemma StaticAboutUU(th: Node)
  requires th.Valid()
  ensures th.uu == 0
  decreases th.Repr
{
  if th.left == null {
  } else { // error: postcondition violation
  }
}

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

  ghost method Theorem0(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == Gauss(n) * Gauss(n);
  {
    if (n != 0) {
      call Theorem0(n-1);
      call Lemma(n-1);
    }
  }

  ghost method Lemma(n: int)
    requires 0 <= n;
    ensures 2 * Gauss(n) == n*(n+1);
  {
    if (n != 0) { call Lemma(n-1); }
  }

  // Here is another proof.  It states the lemma as part of the theorem, and
  // thus proves the two together.

  ghost method Theorem1(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == Gauss(n) * Gauss(n);
    ensures 2 * Gauss(n) == n*(n+1);
  {
    if (n != 0) {
      call Theorem1(n-1);
    }
  }

  // Here is another proof.  It makes use of Dafny's induction heuristics to
  // prove the lemma.

  ghost method Theorem2(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == Gauss(n) * Gauss(n);
  {
    if (n != 0) {
      call Theorem0(n-1);

      assert (forall m :: 0 <= m ==> 2 * Gauss(m) == m*(m+1));
    }
  }

  ghost method M(n: int)
    requires 0 <= n;
  {
    assume (forall k :: 0 <= k && k < n ==> 2 * Gauss(k) == k*(k+1));  // manually assume the induction hypothesis
    assert 2 * Gauss(n) == n*(n+1);
  }

  // Another way to prove the lemma is to supply a postcondition on the Gauss function

  ghost method Theorem3(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == GaussWithPost(n) * GaussWithPost(n);
  {
    if (n != 0) {
      call Theorem3(n-1);
    }
  }

  function GaussWithPost(n: int): int
    requires 0 <= n;
    ensures 2 * GaussWithPost(n) == n*(n+1);
  {
    if n == 0 then 0 else GaussWithPost(n-1) + n
  }

  // Finally, with the postcondition of GaussWithPost, one can prove the entire theorem by induction

  ghost method Theorem4()
    ensures (forall n :: 0 <= n ==> SumOfCubes(n) == GaussWithPost(n) * GaussWithPost(n));
  {
    // look ma, no hints!
  }

  ghost method Theorem5(n: int)
    requires 0 <= n;
    ensures SumOfCubes(n) == GaussWithPost(n) * GaussWithPost(n);
  {
    // the postcondition is a simple consequence of these quantified versions of the theorem:
    if (*) {
      assert (forall m :: 0 <= m ==> SumOfCubes(m) == GaussWithPost(m) * GaussWithPost(m));
    } else {
      call Theorem4();
    }
  }
}

datatype Tree<T> {
  Leaf(T);
  Branch(Tree<T>, Tree<T>);
}

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
}

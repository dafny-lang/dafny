// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Note:  We used integers instead of a generic Comparable type, because
// Dafny has no way of saying that the Comparable type's AtMost function
// is total and transitive.

// Note:  We couldn't get things to work out if we used the Get method.
// Instead, we used .contents.

// Note:  Due to infelicities of the Dafny sequence treatment, we
// needed to supply two lemmas, do a complicated assignment of
// pperm, had to write invariants over p and perm rather than pperm and we couldn't use
// "x in p".

class Queue<T> {
  var contents: seq<T>;
  method Init()
    modifies this;
    ensures |contents| == 0;
  method Enqueue(x: T)
    modifies this;
    ensures contents == old(contents) + [x];
  method Dequeue() returns (x: T)
    requires 0 < |contents|;
    modifies this;
    ensures contents == old(contents)[1..] && x == old(contents)[0];
  function Head(): T
    requires 0 < |contents|;
    reads this;
  { contents[0] }
  function Get(i: int): T
    requires 0 <= i < |contents|;
    reads this;
  { contents[i] }
}

class Comparable {
  ghost function AtMost(c: Comparable): bool
    reads this, c;
}


class Benchmark3 {
  method Sort(q: Queue<int>) returns (r: Queue<int>)
    modifies q;
    ensures fresh(r);
    ensures |r.contents| == |old(q.contents)|;
    ensures forall i, j :: 0 <= i < j < |r.contents| ==> r.Get(i) <= r.Get(j);
    // the final Queue is a permutation of the input Queue
    ensures multiset(r.contents) == multiset(old(q.contents));
  {
    r := new Queue<int>.Init();
    while |q.contents| != 0
      invariant |r.contents| + |q.contents| == |old(q.contents)|;
      invariant forall i, j :: 0 <= i < j < |r.contents| ==> r.contents[i] <= r.contents[j];
      invariant forall i, j ::
                    0 <= i < |r.contents| &&
                    0 <= j < |q.contents|
                    ==> r.contents[i] <= q.contents[j];
      // the current array is that permutation of the input array
      invariant multiset(r.contents + q.contents) == multiset(old(q.contents));
    {
      ghost var qc := q.contents;
      var m,k := RemoveMin(q);
      assert qc == qc[..k] + [m] + qc[k+1..];
      r.Enqueue(m);
    }
  }

  method RemoveMin(q: Queue<int>) returns (m: int, k: int) //m is the min, k is m's index in q
    requires |q.contents| != 0;
    modifies q;
    ensures |old(q.contents)| == |q.contents| + 1;
    ensures 0 <= k < |old(q.contents)| && old(q.contents[k]) == m;
    ensures forall i :: 0 <= i < |q.contents| ==> m <= q.contents[i];
    ensures q.contents == old(q.contents)[k+1..] + old(q.contents)[..k];
  {
    var n := |q.contents|;
    k := 0;
    m := q.Head();
    var j := 0;
    while j < n
      invariant j <= n;
      invariant 0 <= k < n && old(q.contents)[k] == m;
      invariant q.contents == old(q.contents)[j..] + old(q.contents)[..j]; //i.e. rotated
      invariant forall i :: 0 <= i < j ==> m <= old(q.contents)[i]; //m is min so far
    {
      ghost var qc0 := q.contents;
      var x := q.Dequeue();
      q.Enqueue(x);
      RotationLemma(old(q.contents), j, qc0, q.contents);
      if x < m { k := j; m := x; }
      j := j+1;
    }

    Rotate(q, k);

    assert q.contents == old(q.contents)[k..] + old(q.contents)[..k];
    ghost var qq := q.contents;
    m := q.Dequeue();
    assert m == qq[0];
    assert [m] + q.contents == qq && q.contents == qq[1..];
  }

  method Rotate(q: Queue<int>, k: nat)
    requires k <= |q.contents|
    modifies q
    ensures q.contents == old(q.contents)[k..] + old(q.contents)[..k]
  {
    var j := 0;
    while j < k
      invariant j <= k;
      invariant q.contents == old(q.contents)[j..] + old(q.contents)[..j];
    {
      ghost var qc0 := q.contents;
      var x := q.Dequeue();
      q.Enqueue(x);
      RotationLemma(old(q.contents), j, qc0, q.contents);
      j := j+1;
    }
    assert j == k;
  }

  lemma RotationLemma(O: seq, j: nat, A: seq, C: seq)
    requires j < |O|;
    requires A == O[j..] + O[..j];
    requires C == A[1..] + [O[j]];
    ensures C == O[j+1..] + O[..j+1];
  {
    calc {
      A;
      O[j..] + O[..j];
      O[j..j+1] + O[j+1..] + O[..j];
      O[j..j+1] + (O[j+1..] + O[..j]);
    }
    calc {
      C;
      A[1..] + [A[0]];
      { assert A[0] == O[j] && A[1..] == O[j+1..] + O[..j]; }
      O[j+1..] + O[..j] + [O[j]];
      { assert [O[j]] == O[j..j+1]; }
      O[j+1..] + O[..j] + O[j..j+1];
      O[j+1..] + (O[..j] + O[j..j+1]);
      { assert O[..j] + O[j..j+1] == O[..j+1]; }
      O[j+1..] + O[..j+1];
    }
  }
}

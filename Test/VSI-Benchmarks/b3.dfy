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
  function method Head(): T
    requires 0 < |contents|;
    reads this;
  { contents[0] }
  function method Get(i: int): T
    requires 0 <= i && i < |contents|;
    reads this;
  { contents[i] }
}

class Comparable {
  function AtMost(c: Comparable): bool
    reads this, c;
}


class Benchmark3 {

  method Sort(q: Queue<int>) returns (r: Queue<int>, ghost perm: seq<int>)
    requires q != null;
    modifies q;
    ensures r != null && fresh(r);
    ensures |r.contents| == |old(q.contents)|;
    ensures (forall i, j :: 0 <= i && i < j && j < |r.contents| ==>
                r.Get(i) <= r.Get(j));
    //perm is a permutation
    ensures |perm| == |r.contents|; // ==|pperm|
    ensures (forall i :: 0 <= i && i < |perm|==> 0 <= perm[i] && perm[i] < |perm| );
    ensures (forall i, j :: 0 <= i && i < j && j < |perm| ==> perm[i] != perm[j]); 
    // the final Queue is a permutation of the input Queue
    ensures (forall i :: 0 <= i && i < |perm| ==> r.contents[i] == old(q.contents)[perm[i]]);
  {
    r := new Queue<int>.Init();
    ghost var p := [];
    
    var n := 0;
    while (n < |q.contents|)
      invariant n <= |q.contents|;
      invariant n == |p|;
      invariant (forall i :: 0 <= i && i < n ==> p[i] == i);
    {
      p := p + [n];
      n := n + 1;
    }
    perm := [];
    ghost var pperm := p + perm;
   
    while (|q.contents| != 0)
      invariant |r.contents| == |old(q.contents)| - |q.contents|;
      invariant (forall i, j :: 0 <= i && i < j && j < |r.contents| ==>
                    r.contents[i] <= r.contents[j]);
      invariant (forall i, j ::
                    0 <= i && i < |r.contents| &&
                    0 <= j && j < |q.contents|
                    ==> r.contents[i] <= q.contents[j]);
                    
      // pperm is a permutation
      invariant pperm == p + perm && |p| == |q.contents| && |perm| == |r.contents|;
      invariant (forall i :: 0 <= i && i < |perm| ==> 0 <= perm[i] && perm[i] < |pperm|);
      invariant (forall i :: 0 <= i && i < |p| ==> 0 <= p[i] && p[i] < |pperm|);
      invariant (forall i, j :: 0 <= i && i < j && j < |pperm| ==> pperm[i] != pperm[j]);
      // the current array is that permutation of the input array
      invariant (forall i :: 0 <= i && i < |perm| ==> r.contents[i] == old(q.contents)[perm[i]]);
      invariant (forall i :: 0 <= i && i < |p| ==> q.contents[i] == old(q.contents)[p[i]]);
    {  
      var m,k := RemoveMin(q);
      perm := perm + [p[k]]; //adds index of min to perm
      p := p[k+1..] + p[..k]; //remove index of min from p  
      r.Enqueue(m);
      pperm := pperm[k+1..|p|+1] + pperm[..k] + pperm[|p|+1..] + [pperm[k]];
    }
  }
  
  
  method RemoveMin(q: Queue<int>) returns (m: int, k: int) //m is the min, k is m's index in q
    requires q != null && |q.contents| != 0;
    modifies q;
    ensures |old(q.contents)| == |q.contents| + 1;
    ensures  0 <= k && k < |old(q.contents)| && old(q.contents[k]) == m;
    ensures (forall i :: 0 <= i && i < |q.contents| ==> m <= q.contents[i]);
    ensures q.contents == old(q.contents)[k+1..] + old(q.contents)[..k];  
  {
    var n := |q.contents|;
    k := 0;
    m := q.Head(); 
    var j := 0;
   
    while (j < n)
      invariant j <= n;
      invariant q.contents == old(q.contents)[j..] + old(q.contents)[..j]; //i.e. rotated
      invariant 0 <= k && k < |old(q.contents)| && old(q.contents)[k] == m;
      invariant (forall i :: 0<= i && i < j ==> m <= old(q.contents)[i]); //m is min so far
    {
      var x := q.Dequeue();
      q.Enqueue(x);
      if (x < m) { k := j; m := x; }
      j := j+1;
    }
    
    j := 0;
    while (j < k)
      invariant j <= k;
      invariant q.contents == old(q.contents)[j..] + old(q.contents)[..j]; 
    {
      var x := q.Dequeue();
      q.Enqueue(x);
      j := j+1;
    }

    m := q.Dequeue();
  }
}

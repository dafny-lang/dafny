// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

codatatype Stream<T> = Cons(head: T, tail: Stream);

function Tail(s: Stream, n: nat): Stream
{
  if n == 0 then s else Tail(s.tail, n-1)
}
predicate In<T>(x: T, s: Stream<T>)
{
  exists n :: 0 <= n && Tail(s, n).head == x
}
copredicate IsSubStream(s: Stream, u: Stream)
{
  In(s.head, u) && IsSubStream(s.tail, u)
}

lemma Lemma_InTail<T>(x: T, s: Stream<T>)
  requires In(x, s.tail);
  ensures In(x, s);
{
  var n :| 0 <= n && Tail(s.tail, n).head == x;
  assert Tail(s, n+1).head == x;
}
colemma Lemma_TailSubStream(s: Stream, u: Stream)
  requires IsSubStream(s, u.tail);
  ensures IsSubStream(s, u);
{
  Lemma_InTail(s.head, u);
}
lemma Lemma_TailSubStreamK(s: Stream, u: Stream, k: nat)  // this lemma could have been used to prove the previous one
  requires IsSubStream#[k](s, u.tail);
  ensures IsSubStream#[k](s, u);
{
  if k != 0 {
    Lemma_InTail(s.head, u);
    Lemma_TailSubStreamK(s.tail, u, k-1);
  }
}
lemma Lemma_InSubStream<T>(x: T, s: Stream<T>, u: Stream<T>)
  requires In(x, s) && IsSubStream(s, u);
  ensures In(x, u);
{
  var n :| 0 <= n && Tail(s, n).head == x;
  var t := s;
  while n != 0
    invariant 0 <= n;
    invariant Tail(t, n).head == x;
    invariant IsSubStream(t, u);
  {
    t, n := t.tail, n - 1;
  }
}

type PredicateHandle;
predicate P<T>(x: T, h: PredicateHandle)

copredicate AllP(s: Stream, h: PredicateHandle)
{
  P(s.head, h) && AllP(s.tail, h)
}
lemma Lemma_InAllP<T>(x: T, s: Stream<T>, h: PredicateHandle)
  requires In(x, s) && AllP(s, h);
  ensures P(x, h);
{
  var n :| 0 <= n && Tail(s, n).head == x;
  var t := s;
  while n != 0
    invariant 0 <= n;
    invariant Tail(t, n).head == x;
    invariant AllP(t, h);
  {
    t, n := t.tail, n - 1;
  }
}

predicate IsAnother(s: Stream, h: PredicateHandle)
{
  exists n :: 0 <= n && P(Tail(s, n).head, h)
}
copredicate AlwaysAnother(s: Stream, h: PredicateHandle)
{
  IsAnother(s, h) && AlwaysAnother(s.tail, h)
}
colemma Lemma_AllImpliesAlwaysAnother(s: Stream, h: PredicateHandle)
  requires AllP(s, h);
  ensures AlwaysAnother(s, h);
{
  assert Tail(s, 0) == s;
}

function Next(s: Stream, h: PredicateHandle): nat
  requires AlwaysAnother(s, h);
  ensures P(Tail(s, Next(s, h)).head, h);
  ensures forall i :: 0 <= i < Next(s, h) ==> !P(Tail(s, i).head, h);
{
  var n :| 0 <= n && P(Tail(s, n).head, h);
  NextMinimizer(s, h, n)
}
// the following is an auxiliary function of the definition of Next
function NextMinimizer(s: Stream, h: PredicateHandle, n: nat): nat
  requires P(Tail(s, n).head, h);
  ensures P(Tail(s, NextMinimizer(s, h, n)).head, h);
  ensures forall i :: 0 <= i < NextMinimizer(s, h, n) ==> !P(Tail(s, i).head, h);
{
  if forall i :: 0 <= i < n ==> !P(Tail(s, i).head, h) then
    n
  else
    var k :| 0 <= k < n && P(Tail(s, k).head, h);
    NextMinimizer(s, h, k)
}

function Filter(s: Stream, h: PredicateHandle): Stream
  requires AlwaysAnother(s, h);
  decreases Next(s, h);
{
  if P(s.head, h) then
    Cons(s.head, Filter(s.tail, h))
  else
    Filter(s.tail, h)
}
// properties about Filter
colemma Filter_AlwaysAnother(s: Stream, h: PredicateHandle)
  requires AlwaysAnother(s, h);
  ensures AllP(Filter(s, h), h);
  decreases Next(s, h);
{
  if P(s.head, h) {
    Filter_AlwaysAnother(s.tail, h);
  } else {
    Filter_AlwaysAnother#[_k](s.tail, h);
  }
}
colemma Filter_IsSubStream(s: Stream, h: PredicateHandle)
  requires AlwaysAnother(s, h);
  ensures IsSubStream(Filter(s, h), s);
  decreases Next(s, h);
{
  if P(s.head, h) {
    // To prove IsSubStream#[_k](Filter(s, h), s), we prove the two conjuncts from the definition
    calc {
      true;
    ==  { Filter_IsSubStream(s.tail, h); }  // induction hypothesis
      IsSubStream#[_k-1](Filter(s.tail, h), s.tail);
    == // { assert Filter(s.tail, h) == Filter(s, h).tail; }
      IsSubStream#[_k-1](Filter(s, h).tail, s.tail);
    ==> { Lemma_TailSubStreamK(Filter(s, h).tail, s, _k-1); }
      IsSubStream#[_k-1](Filter(s, h).tail, s);
    }
    calc {
      In(Filter(s, h).head, s);
    ==  { assert Filter(s, h) == Cons(s.head, Filter(s.tail, h)); }
      In(s.head, s);
    ==  { assert Tail(s, 0) == s;
          assert exists n :: 0 <= n && Tail(s, n).head == s.head;
        }
      true;
    }
  } else {
    Lemma_TailSubStreamK(Filter(s.tail, h), s, _k);
  }
}

// The following says nothing about the order of the elements in the stream
lemma Theorem_Filter<T>(s: Stream<T>, h: PredicateHandle)
  requires AlwaysAnother(s, h);
  ensures forall x :: In(x, Filter(s, h)) <==> In(x, s) && P(x, h);
{
  forall x
    ensures In(x, Filter(s, h)) <==> In(x, s) && P(x, h);
  {
    if In(x, Filter(s, h)) {
      FS_Ping(s, h, x);
    }
    if In(x, s) && P(x, h) {
      var k :| 0 <= k && Tail(s, k).head == x;
      FS_Pong(s, h, x, k);
    }
  }
}

lemma FS_Ping<T>(s: Stream<T>, h: PredicateHandle, x: T)
  requires AlwaysAnother(s, h) && In(x, Filter(s, h));
  ensures In(x, s) && P(x, h);
{
  Filter_IsSubStream(s, h);
  Lemma_InSubStream(x, Filter(s, h), s);

  Filter_AlwaysAnother(s, h);
  assert AllP(Filter(s, h), h);
  Lemma_InAllP(x, Filter(s, h), h);
}

lemma FS_Pong<T>(s: Stream<T>, h: PredicateHandle, x: T, k: nat)
  requires AlwaysAnother(s, h) && In(x, s) && P(x, h);
  requires Tail(s, k).head == x;
  ensures In(x, Filter(s, h));
  decreases k;
{
  var fs := Filter(s, h);
  if s.head == x {
    assert Tail(fs, 0) == fs;
  } else if P(s.head, h) {
    assert fs == Cons(s.head, Filter(s.tail, h));  // reminder of where we are
    calc {
      true;
    ==  { FS_Pong(s.tail, h, x, k-1); }
      In(x, Filter(s.tail, h));
    ==> { assert fs.head != x;  Lemma_InTail(x, fs); }
      In(x, fs);
    }
  } else {
    assert fs == Filter(s.tail, h);  // reminder of where we are
    FS_Pong(s.tail, h, x, k-1);
  }
}

// ----- orderings ------

function Ord<T>(x: T, ord: PredicateHandle): int

copredicate Increasing(s: Stream, ord: PredicateHandle)
{
  Ord(s.head, ord) < Ord(s.tail.head, ord) && Increasing(s.tail, ord)
}
copredicate IncrFrom(s: Stream, low: int, ord: PredicateHandle)
{
  low <= Ord(s.head, ord) && IncrFrom(s.tail, Ord(s.head, ord) + 1, ord)
}

colemma Lemma_Incr0(s: Stream, low: int, ord: PredicateHandle)
  requires IncrFrom(s, low, ord);
  ensures Increasing(s, ord);
{
}
colemma Lemma_Incr1(s: Stream, ord: PredicateHandle)
  requires Increasing(s, ord);
  ensures IncrFrom(s, Ord(s.head, ord), ord);
{
  Lemma_Incr1(s.tail, ord);
}

lemma Theorem_FilterPreservesOrdering(s: Stream, h: PredicateHandle, ord: PredicateHandle)
  requires Increasing(s, ord) && AlwaysAnother(s, h);
  ensures Increasing(Filter(s, h), ord);
{
  Lemma_Incr1(s, ord);
  Lemma_FilterPreservesIncrFrom(s, h, Ord(s.head, ord), ord);
  Lemma_Incr0(Filter(s, h), Ord(s.head, ord), ord);
}
colemma Lemma_FilterPreservesIncrFrom(s: Stream, h: PredicateHandle, low: int, ord: PredicateHandle)
  requires IncrFrom(s, low, ord) && AlwaysAnother(s, h) && low <= Ord(s.head, ord);
  ensures IncrFrom(Filter(s, h), low, ord);
  decreases Next(s, h);
{
  if P(s.head, h) {
    Lemma_FilterPreservesIncrFrom(s.tail, h, Ord(s.head, ord)+1, ord);
  } else {
    Lemma_FilterPreservesIncrFrom#[_k](s.tail, h, low, ord);
  }
}

// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

codatatype Stream<T> = Cons(head: T, tail: Stream)

function Tail(s: Stream, n: nat): Stream
{
  if n == 0 then s else Tail(s.tail, n-1)
}
predicate In<T>(x: T, s: Stream<T>)
{
  exists n :: 0 <= n && Tail(s, n).head == x
}
greatest predicate IsSubStream[nat](s: Stream, u: Stream)
{
  In(s.head, u) && IsSubStream(s.tail, u)
}

lemma Lemma_InTail<T>(x: T, s: Stream<T>)
  requires In(x, s.tail)
  ensures In(x, s)
{
  var n :| 0 <= n && Tail(s.tail, n).head == x;
  assert Tail(s, n+1).head == x;
}
greatest lemma Lemma_TailSubStream[nat](s: Stream, u: Stream)
  requires IsSubStream(s, u.tail)
  ensures IsSubStream(s, u)
{
  Lemma_InTail(s.head, u);
}
lemma Lemma_TailSubStreamK(s: Stream, u: Stream, k: nat)  // this lemma could have been used to prove the previous one
  requires IsSubStream#[k](s, u.tail)
  ensures IsSubStream#[k](s, u)
{
  if k != 0 {
    Lemma_InTail(s.head, u);
    //Lemma_TailSubStreamK(s.tail, u, k-1);
  }
}
lemma Lemma_InSubStream<T>(x: T, s: Stream<T>, u: Stream<T>)
  requires In(x, s) && IsSubStream(s, u)
  ensures In(x, u)
{
  var n :| 0 <= n && Tail(s, n).head == x;
  var t := s;
  while n != 0
    invariant 0 <= n
    invariant Tail(t, n).head == x
    invariant IsSubStream(t, u)
  {
    t, n := t.tail, n - 1;
  }
}

type Predicate<!T> = T -> bool

greatest predicate AllP(s: Stream, P: Predicate)
{
  P(s.head) && AllP(s.tail, P)
}
lemma Lemma_InAllP<T>(x: T, s: Stream<T>, P: Predicate)
  requires In(x, s) && AllP(s, P)
  ensures P(x)
{
  var n :| 0 <= n && Tail(s, n).head == x;
  var t := s;
  while n != 0
    invariant 0 <= n
    invariant Tail(t, n).head == x
    invariant AllP(t, P)
  {
    t, n := t.tail, n - 1;
  }
}

predicate IsAnother(s: Stream, P: Predicate)
{
  exists n :: 0 <= n && P(Tail(s, n).head)
}
greatest predicate AlwaysAnother(s: Stream, P: Predicate)
{
  IsAnother(s, P) && AlwaysAnother(s.tail, P)
}
greatest lemma Lemma_AllImpliesAlwaysAnother(s: Stream, P: Predicate)
  requires AllP(s, P)
  ensures AlwaysAnother(s, P)
{
  assert Tail(s, 0) == s;
}

function Next(s: Stream, P: Predicate): nat
  requires AlwaysAnother(s, P)
  ensures P(Tail(s, Next(s, P)).head)
  ensures forall i :: 0 <= i < Next(s, P) ==> !P(Tail(s, i).head)
{
  var n :| 0 <= n && P(Tail(s, n).head);
  NextMinimizer(s, P, n)
}
// the following is an auxiliary function of the definition of Next
function NextMinimizer(s: Stream, P: Predicate, n: nat): nat
  requires P(Tail(s, n).head)
  ensures P(Tail(s, NextMinimizer(s, P, n)).head)
  ensures forall i :: 0 <= i < NextMinimizer(s, P, n) ==> !P(Tail(s, i).head)
{
  if forall i :: 0 <= i < n ==> !P(Tail(s, i).head) then
    n
  else
    var k :| 0 <= k < n && P(Tail(s, k).head);
    NextMinimizer(s, P, k)
}

lemma NextLemma(s: Stream, P: Predicate)
  requires AlwaysAnother(s, P) && !P(s.head)
  ensures Next(s.tail, P) < Next(s, P)
{
  assert forall i :: 0 < i ==> Tail(s, i) == Tail(s.tail, i-1);
}

function Filter(s: Stream, P: Predicate): Stream
  requires AlwaysAnother(s, P)
  decreases Next(s, P)
{
  if P(s.head) then
    Cons(s.head, Filter(s.tail, P))
  else
    NextLemma(s, P);
    Filter(s.tail, P)
}
// properties about Filter
greatest lemma Filter_AlwaysAnother(s: Stream, P: Predicate)
  requires AlwaysAnother(s, P)
  ensures AllP(Filter(s, P), P)
  decreases Next(s, P)
{
  if P(s.head) {
    Filter_AlwaysAnother(s.tail, P);
  } else {
    NextLemma(s, P);
    Filter_AlwaysAnother#[_k](s.tail, P);
  }
}
greatest lemma Filter_IsSubStream[nat](s: Stream, P: Predicate)
  requires AlwaysAnother(s, P)
  ensures IsSubStream(Filter(s, P), s)
  decreases Next(s, P)
{
  if P(s.head) {
    // To prove IsSubStream#[_k](Filter(s, h), s), we prove the two conjuncts from the definition
    calc {
      true;
    ==  { Filter_IsSubStream(s.tail, P); }  // induction hypothesis
      IsSubStream(Filter(s.tail, P), s.tail);
    == // { assert Filter(s.tail, h) == Filter(s, h).tail; }
      IsSubStream(Filter(s, P).tail, s.tail);
    ==> { Lemma_TailSubStreamK(Filter(s, P).tail, s, _k-1); }
      IsSubStream(Filter(s, P).tail, s);
    }
    calc {
      In(Filter(s, P).head, s);
    ==  { assert Filter(s, P) == Cons(s.head, Filter(s.tail, P)); }
      In(s.head, s);
    ==  { assert Tail(s, 0) == s;
          assert exists n :: 0 <= n && Tail(s, n).head == s.head;
        }
      true;
    }
  } else {
    NextLemma(s, P);
    Lemma_TailSubStreamK(Filter(s.tail, P), s, _k);
  }
}

// The following says nothing about the order of the elements in the stream
lemma Theorem_Filter<T>(s: Stream<T>, P: Predicate)
  requires AlwaysAnother(s, P)
  ensures forall x :: In(x, Filter(s, P)) <==> In(x, s) && P(x)
{
  forall x
    ensures In(x, Filter(s, P)) <==> In(x, s) && P(x)
  {
    if In(x, Filter(s, P)) {
      FS_Ping(s, P, x);
    }
    if In(x, s) && P(x) {
      var k :| 0 <= k && Tail(s, k).head == x;
      FS_Pong(s, P, x, k);
    }
  }
}

lemma FS_Ping<T>(s: Stream<T>, P: Predicate, x: T)
  requires AlwaysAnother(s, P) && In(x, Filter(s, P))
  ensures In(x, s) && P(x)
{
  Filter_IsSubStream(s, P);
  Lemma_InSubStream(x, Filter(s, P), s);

  Filter_AlwaysAnother(s, P);
  assert AllP(Filter(s, P), P);
  Lemma_InAllP(x, Filter(s, P), P);
}

lemma FS_Pong<T>(s: Stream<T>, P: Predicate, x: T, k: nat)
  requires AlwaysAnother(s, P) && In(x, s) && P(x)
  requires Tail(s, k).head == x
  ensures In(x, Filter(s, P))
  decreases k
{
  var fs := Filter(s, P);
  if s.head == x {
    assert Tail(fs, 0) == fs;
  } else if P(s.head) {
    assert fs == Cons(s.head, Filter(s.tail, P));  // reminder of where we are
    calc {
      true;
    ==  { FS_Pong(s.tail, P, x, k-1); }
      In(x, Filter(s.tail, P));
    ==> { assert fs.head != x;  Lemma_InTail(x, fs); }
      In(x, fs);
    }
  } else {
    assert fs == Filter(s.tail, P);  // reminder of where we are
    //FS_Pong(s.tail, h, x, k-1);
  }
}

// ----- orderings ------

type Ord<!T> = T -> int

greatest predicate Increasing(s: Stream, ord: Ord)
{
  ord(s.head) < ord(s.tail.head) && Increasing(s.tail, ord)
}
greatest predicate IncrFrom[nat](s: Stream, low: int, ord: Ord)
{
  low <= ord(s.head) && IncrFrom(s.tail, ord(s.head) + 1, ord)
}

greatest lemma Lemma_Incr0(s: Stream, low: int, ord: Ord)
  requires IncrFrom(s, low, ord)
  ensures Increasing(s, ord)
{
}
greatest lemma Lemma_Incr1[nat](s: Stream, ord: Ord)
  requires Increasing(s, ord)
  ensures IncrFrom(s, ord(s.head), ord)
{
  Lemma_Incr1(s.tail, ord);
}

lemma Theorem_FilterPreservesOrdering(s: Stream, P: Predicate, ord: Ord)
  requires Increasing(s, ord) && AlwaysAnother(s, P)
  ensures Increasing(Filter(s, P), ord)
{
  Lemma_Incr1(s, ord);
  Lemma_FilterPreservesIncrFrom(s, P, ord(s.head), ord);
  Lemma_Incr0(Filter(s, P), ord(s.head), ord);
}
greatest lemma Lemma_FilterPreservesIncrFrom[nat](s: Stream, P: Predicate, low: int, ord: Ord)
  requires IncrFrom(s, low, ord) && AlwaysAnother(s, P) && low <= ord(s.head)
  ensures IncrFrom(Filter(s, P), low, ord)
  decreases Next(s, P)
{
  if P(s.head) {
    Lemma_FilterPreservesIncrFrom(s.tail, P, ord(s.head)+1, ord);
  } else {
    NextLemma(s, P);
    Lemma_FilterPreservesIncrFrom#[_k](s.tail, P, low, ord);
  }
}

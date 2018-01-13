// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// --------------------------------------------------

module TestInductiveDatatypes
{
  // The following types test for cycles that go via instantiated type arguments

  datatype Record<T> = Ctor(T)

  datatype RecInt = Ctor(Record<int>)  // this is fine
  datatype Rec_Forever = Ctor(Record<Rec_Forever>)  // error
  datatype Rec_Stops = Cons(Record<Rec_Stops>, Rec_Stops) | Nil  // this is okay

  datatype D<T> = Ctor(E<D<T>>)  // error: illegal cycle
  datatype E<T> = Ctor(T)

  // the following is okay
  datatype MD<T> = Ctor(ME<T>)
  datatype ME<T> = Ctor(T)
  method M()
  {
    var d: MD<MD<int>>;
  }

  datatype A = Ctor(B)  // superficially looks like a cycle, but can still be constructed
  datatype B = Ctor(List<A>)
  datatype List<T> = Nil | Cons(T, List)
}

module MoreInductive {
  datatype Tree<G> = Node(G, List<Tree<G>>)
  datatype List<T> = Nil | Cons(T, List<T>)

  datatype M = All(List<M>)
  datatype H<'a> = HH('a, Tree<'a>)
  datatype K<'a> = KK('a, Tree<K<'a>>)  // error
  datatype L<'a> = LL('a, Tree<List<L<'a>>>)
}

// --------------------------------------------------

module TestCoinductiveDatatypes
{
  codatatype InfList<T> = Done | Continue(T, InfList)

  codatatype Stream<T> = More(T, Stream<T>)

  codatatype BinaryTreeForever<T> = BNode(val: T, left: BinaryTreeForever<T>, right: BinaryTreeForever<T>)

  datatype List<T> = Nil | Cons(T, List)

  codatatype BestBushEver<T> = Node(value: T, branches: List<BestBushEver<T>>)

  codatatype LazyRecord<T> = Lazy(contents: T)
  class MyClass<T> { }
  datatype GenericDt<T> = Blue | Green(T)
  datatype GenericRecord<T> = Rec(T)

  datatype FiniteEnough_Class = Ctor(MyClass<FiniteEnough_Class>)
  datatype FiniteEnough_Co = Ctor(LazyRecord<FiniteEnough_Co>)
  datatype FiniteEnough_Dt = Ctor(GenericDt<FiniteEnough_Dt>)  // fine
  datatype NotFiniteEnough_Dt = Ctor(GenericRecord<NotFiniteEnough_Dt>)  // error

}

// --------------- CoPredicates --------------------------

module CoPredicateResolutionErrors {

  codatatype Stream<T> = StreamCons(head: T, tail: Stream)

  function Upward(n: int): Stream<int>
  {
    StreamCons(n, Upward(n + 1))
  }

  function Doubles(n: int): Stream<int>
  {
    StreamCons(2*n, Doubles(n + 1))
  }

  copredicate Pos(s: Stream<int>)
  {
    0 < s.head && Pos(s.tail) && Even(s)
  }

  copredicate Even(s: Stream<int>)
  {
    s.head % 2 == 0 && Even(s.tail)
    && (s.head == 17 ==> Pos(s))
    && (Pos(s) ==> s.head == 17)  // error: cannot make recursive copredicate call in negative position
    && !Even(s)  // error: cannot make recursive copredicate call in negative position
    && (Even(s) <==> Even(s))  // error (x2): recursive copredicate calls allowed only in positive positions
  }

  copredicate CP[nat](i: int)
  {
    CP(i) &&
    !CP(i) &&  // error: not in a positive position
    (forall j :: CP(j)) &&
    (exists k :: 0 <= k < i*i && CP(k)) &&
    (exists k :: 0 <= k && CP(k)) &&  // error: unbounded range
    (exists k :: k < i*i && CP(k)) &&  // error: unbounded range
    (exists l :: CP(l))  // error: unbounded range
  }

  copredicate CQ(i: int, j: int)
  {
    exists i :: i == 6 && if j % 2 == 0 then CQ(i, i) else CQ(j, j)
  }

  copredicate CR(i: int, j: int)
  {
    exists i :: i == if CR(i, j) then 6 else j  // error: not allowed to call CR recursively here
  }

  copredicate CS(i: int, j: int)
  {
    exists i ::
      i <= (if CS(i, j) then 6 else j) &&  // error: not allowed to call CS recursively here
      (if CS(i, j) then 6 else j) <= i     // error: not allowed to call CS recursively here
  }

  copredicate Another(s: Stream<int>)
  {
    !Even(s)  // here, negation is fine
  }

  ghost method Lemma(n: int)
    ensures Even(Doubles(n))
  {
  }

  copredicate CoStmtExpr_Good(s: Stream<int>)
  {
    s.head > 0 && (MyLemma(s.head); CoStmtExpr_Good(s.tail))
  }

  lemma MyLemma(x: int)
  {
  }

  copredicate CoStmtExpr_Bad(s: Stream<int>)
  {
    s.head > 0 &&
    (MyRecursiveLemma(s.head);  // error: cannot call method recursively from copredicate
     CoStmtExpr_Bad(s.tail))
  }

  lemma MyRecursiveLemma(x: int)
  {
    var p := CoStmtExpr_Bad(Upward(x));
  }
}

// --------------------------------------------------

module UnfruitfulCoLemmaConclusions {
  codatatype Stream<T> = Cons(head: T, tail: Stream)

  copredicate Positive(s: Stream<int>)
  {
    s.head > 0 && Positive(s.tail)
  }

  colemma BadTheorem(s: Stream)
    ensures false;
  {
    BadTheorem(s.tail);
  }

  colemma CM(s: Stream<int>)
    ensures true && !false;
    ensures s.head == 8 ==> Positive(s);
    ensures s.tail == s;
    ensures s.head < 100;
    ensures Positive(s) ==> s.tail == s;
    ensures Positive(s) ==> s.head > 88;
    ensures !Positive(s) ==> s.tail == s;
    ensures !(true && !false ==> Positive(s) && !Positive(s));
    ensures !(false && !true ==> Positive(s) && !Positive(s));
  {
  }
}

// --------------- Inductive Predicates --------------------------

module InductivePredicateResolutionErrors {

  datatype List<T> = Nil | Cons(head: T, tail: List)
  codatatype IList<T> = INil | ICons(head: T, tail: IList)

  inductive predicate Pos(s: List<int>)
  {
    s.Cons? && 0 < s.head && Pos(s.tail) && Even(s)
  }

  inductive predicate Even(s: List<int>)
  {
    s.Cons? && s.head % 2 == 0 && Even(s.tail)
    && (s.head == 17 ==> Pos(s))
    && (Pos(s) ==> s.head == 17)  // error: cannot make recursive inductive-predicate call in negative position
    && !Even(s)  // error: cannot make recursive inductive-predicate call in negative position
    && (Even(s) <==> Even(s))  // error (x2): recursive inductive-predicate calls allowed only in positive positions
  }

  inductive predicate LetSuchThat(s: List<int>)
  {
    if s != Nil then true else
      var h :| h == s.head;
      h < 0 && LetSuchThat(s.tail)  // this is fine for an inductive predicate
  }
  copredicate CoLetSuchThat(s: IList<int>)
  {
    if s != INil then true else
      var h :| h == s.head;
      h < 0 && CoLetSuchThat(s.tail)  // error: recursive call to copredicate in body of let-such-that
  }

  inductive predicate NegatedLetSuchThat(s: List<int>)
  {
    if s != Nil then true else
      !var h :| h == s.head;
      h < 0 && !NegatedLetSuchThat(s.tail)  // error: recursive call to inductive predicate in body of let-such-that
  }
  copredicate NegatedCoLetSuchThat(s: IList<int>)
  {
    if s != INil then true else
      !var h :| h == s.head;
      h < 0 && !NegatedCoLetSuchThat(s.tail)  // this is fine for a coinductive predicate
  }

  inductive predicate CP[nat](i: int)
  {
    CP(i) &&
    !CP(i) &&  // error: not in a positive position
    (exists j :: CP(j)) &&
    (forall k :: 0 <= k < i*i ==> CP(k)) &&
    (forall k :: 0 <= k ==> CP(k)) &&  // error: unbounded range
    (forall k :: k < i*i ==> CP(k)) &&  // error: unbounded range
    (forall l :: CP(l))  // error: unbounded range
  }

  inductive predicate CQ(i: int, j: int)
  {
    forall i :: i == 6 ==> if j % 2 == 0 then CQ(i, i) else CQ(j, j)
  }

  inductive predicate CR(i: int, j: int)
  {
    i == if CR(i, j) then 6 else j  // error: not allowed to call CR recursively here
  }

  inductive predicate CS(i: int, j: int)
  {
    forall i ::
      i <= (if CS(i, j) then 6 else j) &&  // error: not allowed to call CS recursively here
      (if CS(i, j) then 6 else j) <= i     // error: not allowed to call CS recursively here
  }

  inductive predicate Another(s: List<int>)
  {
    !Even(s)  // here, negation is fine
  }

  inductive predicate IndStmtExpr_Good(s: List<int>)
  {
    s.head > 0 && (MyLemma(s.head); IndStmtExpr_Good(s.tail))
  }

  lemma MyLemma(x: int)
  {
  }

  inductive predicate IndStmtExpr_Bad(s: List<int>)
  {
    s.Cons? && s.head > 0 &&
    (MyRecursiveLemma(s.head);  // error: cannot call method recursively from inductive predicate
     IndStmtExpr_Bad(s.tail))
  }

  lemma MyRecursiveLemma(x: int)
  {
    var p := IndStmtExpr_Bad(Cons(x, Nil));
  }
}


// --------------- calls between [ORDINAL] and [nat] --------------------------

// predicate-to-predicate call
module TypeOfK_Pred_to_Pred {
  inductive predicate A[ORDINAL](x: int) {
    B(x)  // error: cannot call from [ORDINAL] to [nat]
  }
  inductive predicate B[nat](x: int) {
    A(x)  // error: cannot call from [nat] to [ORDINAL]
  }
}

// lemma-to-predicate call
module TypeOfK_Lemma_to_Pred {
  inductive predicate E[ORDINAL](x: int)
  inductive lemma LE[nat](x: int)
    requires E(x)  // error: cannot call from [nat] to [ORDINAL]
  {
  }

  inductive predicate F[nat](x: int)
  inductive lemma LF[ORDINAL](x: int)
    requires F(x)  // error: cannot call from [ORDINAL] to [nat]
  {
  }
}

// lemma-to-lemma call
module TypeOfK_Lemma_to_Lemma {
  inductive lemma G[ORDINAL](x: int)
    ensures x == 8
  {
    H(x);  // error: cannot call from [ORDINAL] to [nat]
  }

  inductive lemma H[nat](x: int)
    ensures x == 8
  {
    G(x);  // error: cannot call from [nat] to [ORDINAL]
  }
}

module Continuity {
  datatype cmd = Inc | Seq(cmd, cmd) | Repeat(cmd)
  type state = int

  copredicate BigStep(c: cmd, s: state, t: state)
  {
    match c
    case Inc =>
      t == s + 1
    case Seq(c0, c1) =>
      exists s' :: BigStep(c0, s, s') && BigStep(c1, s', t)  // fine
    case Repeat(body) =>
      s == t ||
      exists s' :: BigStep(body, s, s') && BigStep(c, s', t)  // fine
  }

  copredicate NatBigStep[nat](c: cmd, s: state, t: state)
  {
    match c
    case Inc =>
      t == s + 1
    case Seq(c0, c1) =>
      exists s' :: NatBigStep(c0, s, s') && NatBigStep(c1, s', t)  // error (x2): continuity violation
    case Repeat(body) =>
      s == t ||
      exists s' :: NatBigStep(body, s, s') && NatBigStep(c, s', t)  // error (x2): continuity violation
  }
}

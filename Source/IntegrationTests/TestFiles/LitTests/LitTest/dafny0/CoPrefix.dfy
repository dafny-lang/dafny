// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s" -- --allow-deprecation


// ----- Stream

codatatype Stream = Nil | Cons(head: int, tail: Stream)

ghost function append(M: Stream, N: Stream): Stream
{
  match M
  case Nil => N
  case Cons(t, M') => Cons(t, append(M', N))
}

ghost function zeros(): Stream
{
  Cons(0, zeros())
}

ghost function ones(): Stream
{
  Cons(1, ones())
}

greatest predicate atmost(a: Stream, b: Stream)
{
  match a
  case Nil => true
  case Cons(h,t) => b.Cons? && h <= b.head && atmost(t, b.tail)
}

greatest lemma {:induction false} Theorem0()
  ensures atmost(zeros(), ones());
{
  // the following shows two equivalent ways to getting essentially the
  // co-inductive hypothesis
  if (*) {
    Theorem0#[_k-1]();
  } else {
    Theorem0();
  }
}

lemma Theorem0_Manual()
  ensures atmost(zeros(), ones());
{
  forall k: ORDINAL {
    Theorem0_Lemma(k);
  }
}

datatype Natural = Zero | Succ(Natural)

greatest lemma {:induction false} Theorem0_TerminationFailure_ExplicitDecreases(y: Natural)
  ensures atmost(zeros(), ones());
  decreases y;
{
  match (y) {
    case Succ(x) =>
      // this is just to show that the decreases clause does kick in
      Theorem0_TerminationFailure_ExplicitDecreases#[_k](x);
    case Zero =>
      Theorem0_TerminationFailure_ExplicitDecreases#[_k](y);  // error: failure to terminate
  }
  Theorem0_TerminationFailure_ExplicitDecreases#[_k-1](y);
}

greatest lemma {:induction false} Theorem0_TerminationFailure_DefaultDecreases(y: Natural)
  ensures atmost(zeros(), ones());
{
  match (y) {
    case Succ(yy) =>
      // this is just to show that the decreases clause does kick in
      Theorem0_TerminationFailure_DefaultDecreases#[_k](yy);
    case Zero =>
      Theorem0_TerminationFailure_DefaultDecreases#[_k](y);  // error: failure to terminate
  }
  Theorem0_TerminationFailure_DefaultDecreases#[_k-1](y);
}

lemma {:induction true} Theorem0_Lemma(k: ORDINAL)
  ensures atmost#[k](zeros(), ones());
{
}

greatest lemma {:induction false} Theorem1()
  ensures append(zeros(), ones()) == zeros();
{
  Theorem1();
}

codatatype IList = ICons(head: int, tail: IList)

ghost function UpIList(n: int): IList
{
  ICons(n, UpIList(n+1))
}

greatest predicate Pos(s: IList)
{
  s.head > 0 && Pos(s.tail)
}

greatest lemma {:induction false} Theorem2(n: int)
  requires 1 <= n;
  ensures Pos(UpIList(n));
{
  Theorem2(n+1);
}

greatest lemma {:induction false} Theorem2_NotAProof(n: int)
  requires 1 <= n;
  ensures Pos(UpIList(n));
{  // error: this is not a proof (without automatic induction)
}

codatatype TList<T> = TCons(head: T, tail: TList)

ghost function Next<T>(t: T): T

ghost function FF<T>(h: T): TList<T>
{
  TCons(h, FF(Next(h)))
}

ghost function GG<T>(h: T): TList<T>
{
  TCons(h, GG(Next(h)))
}

greatest lemma {:induction false} Compare<T>(h: T)
  ensures FF(h) == GG(h);
{
  assert FF(h).head == GG(h).head;
  Compare(Next(h));
  if {
    case true =>
      assert FF(h).tail == GG(h).tail;  // yes, this full equality is a focal predicate, so it's rewritten into ==#[_k - 1]
    case true =>
      assert FF(h) ==#[_k] GG(h);  // yes, this is the postcondition to be proved, and it is known to hold
    case true =>
      assert FF(h).tail ==#[_k] GG(h).tail;  // error: only _k-1 equality of the tails is known here
    case true =>
      assert FF(h).tail ==#[_k - 1] GG(h).tail;  // yes, follows from call to Compare
    case true =>
  }
}

greatest lemma {:induction false} BadTheorem(s: IList)
  ensures false;
{  // error: postcondition violation
  BadTheorem(s.tail);
}

// ---------------------------------

// Make sure recursive calls get checked for termination
module Recursion {
  greatest lemma X() { Y(); }
  greatest lemma Y() { X(); }

  greatest lemma G(x: int)
    ensures x < 100;
  {  // error: postcondition violation (when _k == 0)
    H(x);
  }
  greatest lemma H(x: int)
    ensures x < 100;
  {  // error: postcondition violation (when _k == 0)
    G(x);
  }

  greatest lemma A(x: int) { B(x); }
  greatest lemma B(x: int)
  {
    A#[10](x);  // error: this is a recursive call, and the termination metric may not be going down
  }

  greatest lemma A'(x: int) { B'(x); }
  greatest lemma B'(x: int)
  {
    if (10 < _k) {
      A'#[10](x);
    }
  }

  greatest lemma A''(x: int) { B''(x); }
  greatest lemma B''(x: int)
  {
    if (0 < x) {
      A''#[_k](x-1);
    }
  }
}

module PrefixEquality {
  codatatype Stream<T> = Cons(head: T, Stream)

  greatest lemma Test0(s: Stream, t: Stream)
    requires s.head == t.head
  {
    calc {
      s;
      ==#[_k-1]
      t;  // error: this step might not hold
      ==#[if 2 <= _k.Offset then _k-2 else _k-1]
      s;  // error: this step might not hold
      ==#[0]
      t;
    }
  }

  greatest lemma Test1(s: Stream, t: Stream)
    requires s == t
  {
    calc {
      s;
      ==#[_k-1]
      t;
      ==#[_k-2]  // error: the ORDINAL _k might have an .Offset less than 2
      s;
      ==#[0]
      t;
    }
  }
}

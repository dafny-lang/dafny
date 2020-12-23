// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

codatatype Stream<T> = Cons(head: T, tail: Stream)
codatatype IList<T> = Nil | ICons(head: T, tail: IList)

// -----------------------------------------------------------------------

copredicate Pos(s: Stream<int>)
{
  s.head > 0 && Pos(s.tail)
}

function Up(n: int): Stream<int>
{
  Cons(n, Up(n+1))
}

function Inc(s: Stream<int>): Stream<int>
{
  Cons(s.head + 1, Inc(s.tail))
}

lemma {:induction false} UpLemma(k: nat, n: int)
  ensures Inc(Up(n)) ==#[k] Up(n+1);
{
  if (k != 0) {
    UpLemma(k-1, n+1);
  }
}

colemma {:induction false} CoUpLemma(n: int)
  ensures Inc(Up(n)) == Up(n+1);
{
  CoUpLemma(n+1);
}

lemma UpLemma_Auto(k: nat, n: int, nn: int)
  ensures nn == n+1 ==> Inc(Up(n)) ==#[k] Up(nn);  // note: it would be nice to do an automatic rewrite (from "ensures Inc(Up(n)) ==#[k] Up(n+1)") to obtain the good trigger here
{
}

colemma CoUpLemma_Auto(n: int, nn: int)
  ensures nn == n+1 ==> Inc(Up(n)) == Up(nn);  // see comment above
{
}

// -----------------------------------------------------------------------

function Repeat(n: int): Stream<int>
{
  Cons(n, Repeat(n))
}

colemma RepeatLemma(n: int)
  ensures Inc(Repeat(n)) == Repeat(n+1);
{
}

// -----------------------------------------------------------------------

copredicate True(s: Stream)
{
  True(s.tail)
}

colemma AlwaysTrue(s: Stream)
  ensures True(s);
{
}

copredicate AlsoTrue(s: Stream)
{
  AlsoTrue(s)
}

colemma AlsoAlwaysTrue(s: Stream)
  ensures AlsoTrue(s);
{
}

copredicate TT(y: int)
{
  TT(y+1)
}

colemma AlwaysTT(y: int)
  ensures TT(y);
{
}

// -----------------------------------------------------------------------

function Append(M: IList, N: IList): IList
{
  match M
  case Nil => N
  case ICons(x, M') => ICons(x, Append(M', N))
}

function zeros(): IList<int>
{
  ICons(0, zeros())
}

function ones(): IList<int>
{
  ICons(1, ones())
}

copredicate AtMost(a: IList<int>, b: IList<int>)
{
  match a
  case Nil => true
  case ICons(h,t) => b.ICons? && h <= b.head && AtMost(t, b.tail)
}

colemma ZerosAndOnes_Theorem0()
  ensures AtMost(zeros(), ones());
{
}

colemma ZerosAndOnes_Theorem1()
  ensures Append(zeros(), ones()) == zeros();
{
}

// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

// Examples from https://www.haskell.org/tutorial/functions.html

method Main()
{
  var n := 7;
  Print(n, "ones()", ones());
  Print(n, "from(3)", from(3));
  Print(n, "Map(plus1, ones())", Map(plus1, ones()));
  Print(n, "Map(plus1, from(3))", Map(plus1, from(3)));
  Print(n, "squares()", squares());
  PrintList("take(5, from(3))", take(5, from(3)));
  Print(n, "zip(ones(), from(3)", zip(ones(), from(3)));
  Print(n, "addPair(zip(ones(), from(3))", addPair(zip(ones(), from(3))));
  Print(n, "fib()", fib());
  Print(n, "add(ones(), from(3))", add(ones(), from(3)));
  Print(n, "Fib()", Fib());
  Print(n, "Fib0()", Fib0());
  Print(n, "Fib1()", Fib1());
  Print(n, "OhOnes()", OhOnes());
  Print(n, "Combine(plus, ones(), from(3))", Combine(plus, ones(), from(3)));
}

method Print<T>(n: nat, msg: string, s: Stream<T>) {
  print msg, ": ";
  var i, s := 0, s;
  while i < n {
    print s.head, " ";
    i, s := i + 1, s.tail;
  }
  print "...\n";
}

method PrintList<T>(msg: string, s: List<T>) {
  print msg, ": ";
  var s := s;
  while s != Nil
    decreases s
  {
    print s.head, " ";
    s := s.tail;
  }
  print "\n";
}

function plus1(x: int): int { x + 1 }
function plus(x: int, y: int): int { x + y }

datatype List<T> = Nil | ListCons(head: T, tail: List<T>)
codatatype Stream<T> = Cons(head: T, tail: Stream<T>)

function ones(): Stream<int>
{
  Cons(1, ones())
}

function from(n: int): Stream<int>
{
  Cons(n, from(n+1))
}

function Map<T,U>(f: T -> U, s: Stream<T>): Stream<U>
{
  Cons(f(s.head), Map(f, s.tail))
}

function squares(): Stream<int>
{
  Map(x => x*x, from(0))
}

function take(n: nat, s: Stream): List
{
  if n == 0 then Nil else ListCons(s.head, take(n-1, s.tail))
}

function {:abstemious} zip<T,U>(a: Stream<T>, b: Stream<U>): Stream<(T,U)>
{
  Cons((a.head, b.head), zip(a.tail, b.tail))
}

function {:abstemious} addPair(a: Stream<(int,int)>): Stream<int>
{
  Cons(a.head.0 + a.head.1, addPair(a.tail))
}

function fib(): Stream<int>
{
  Cons(0, Cons(1, addPair(zip(fib(), fib().tail))))
}

function {:abstemious} add(a: Stream<int>, b: Stream<int>): Stream<int>
{
  Cons(a.head + b.head, add(a.tail, b.tail))
}

function Fib(): Stream<int>
{
  Cons(0, Cons(1, add(Fib(), Fib().tail)))
}

function Fib0(): Stream<int>
{
  Cons(0, Fib1())
}

function Fib1(): Stream<int>
{
  Cons(1, add(Fib0(), Fib1()))
}

function OhOnes(): Stream<int>
{
  Cons(0, Cons(1, OhOnes().tail))
}

function {:abstemious}
  Combine<T>(f: (T,T) -> T, a: Stream, b: Stream): Stream
{
  Cons(f(a.head, b.head), Combine(f, a.tail, b.tail))
}

// ---- various fun lemmas ----

ghost function nth<T>(n: nat, s: Stream<T>): T
{
  if n == 0 then s.head else nth(n-1, s.tail)
}

ghost function nfib(n: nat): nat
{
  if n < 2 then n else nfib(n-2) + nfib(n-1)
}

lemma Ones_Correct(n: nat)
  ensures nth(n, ones()) == 1
{
}

greatest lemma OhOnesTail_Correct()
  ensures OhOnes().tail == ones()
{
}

lemma OhOnes_Correct()
  ensures OhOnes() == Cons(0, ones())
{
  OhOnesTail_Correct();
}

lemma OhOnes_Correct'(n: nat)
  ensures nth(n, OhOnes()) == if n == 0 then 0 else 1
{
  OhOnes_Correct();
  if n != 0 {
    Ones_Correct(n-1);
  }
}

lemma C_Correct(n: nat, k: int)
  ensures nth(n, Combine(plus, ones(), from(k))) == k + 1 + n
{
}

greatest lemma CombinePlus_Correct(a: Stream<int>, b: Stream<int>)
  ensures Combine(plus, a, b) == add(a, b)
{
}

lemma add_Correct(n: nat, a: Stream<int>, b: Stream<int>)
  ensures nth(n, add(a, b)) == nth(n, a) + nth(n, b)
{
}

ghost function StraightFibonacci(n: nat): Stream<int>
{
  Cons(nfib(n), StraightFibonacci(n+1))
}

lemma StraightFibonacci_Correct(n: nat, k: nat)
  ensures nth(n, StraightFibonacci(k)) == nfib(k + n)
{
}

lemma Fib_Correct(n: nat)
  ensures nth(n, Fib()) == nfib(n)
{
  if n < 2 {
  } else {
    var F  := Fib();
    calc {
      nth(n, F);
    ==
      nth(n-2, F.tail.tail);
    ==
      nth(n-2, add(Fib(), Fib().tail));
    ==  { add_Correct(n-2, Fib(), Fib().tail); }
      nth(n-2, Fib()) + nth(n-2, Fib().tail);
    ==
      nth(n-2, Fib()) + nth(n-1, Fib());
    ==  { Fib_Correct(n-2); Fib_Correct(n-1); }
      nfib(n-2) + nfib(n-1);
    ==
      nfib(n);
    }
  }
}

// --------------- ternary expression is a trigger ---------------

lemma OrdinalLemma(k: ORDINAL)
  ensures OhOnes().tail ==#[k] ones()
{
  // automatic induction on k
}

lemma NaturalLemma(k: nat)
  ensures OhOnes().tail ==#[k] ones()
{
  // automatic induction on k
}

lemma Quantifier()
  // the following quantifiers use the entire body as a trigger (previously, ternary expressions
  // had not been considered as trigger candidates)
  requires forall k: nat :: OhOnes().tail ==#[k] ones()
  requires forall k: ORDINAL :: OhOnes().tail ==#[k] ones()
{
}

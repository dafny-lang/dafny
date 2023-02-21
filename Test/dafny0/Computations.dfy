// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function fact6(n: nat): nat
{
  fact(n+6)
}

ghost function fact(n: nat): nat
{
  if (n==0) then 1 else n*fact(n-1)
}
ghost method compute_fact6()
  ensures fact(6)==720;
{
}
ghost method compute_fact6_plus()
  ensures fact6(0)==720;
{
}

datatype intlist = IntNil | IntCons(head: int, tail: intlist)
ghost function intsize(l: intlist): nat
{
  if (l.IntNil?) then 0 else 1+intsize(l.tail)
}
ghost function intapp(a: intlist, b: intlist): intlist
{
  if (a.IntNil?) then b else IntCons(a.head, intapp(a.tail, b))
}
ghost method compute_intappsize()
  ensures intsize(intapp(IntCons(1, IntCons(2, IntNil)), IntCons(3, IntCons(4, IntNil))))==4;
{
}
ghost method compute_intsize4()
  ensures intsize(IntCons(1, IntCons(2, IntCons(3, IntCons(4, IntNil))))) == 4;
{
}
ghost function cintsize(l: intlist): nat
{
  match l
  case IntNil => 0
  case IntCons(hd, tl) => 1+cintsize(tl)
}
ghost function cintapp(a: intlist, b: intlist): intlist
{
  match a
  case IntNil => b
  case IntCons(hd, tl) => IntCons(hd, cintapp(tl, b))
}
ghost method compute_cintappsize()
  ensures cintsize(cintapp(IntCons(1, IntCons(2, IntNil)), IntCons(3, IntCons(4, IntNil))))==4;
{
}
ghost method compute_cintsize4()
  ensures cintsize(IntCons(1, IntCons(2, IntCons(3, IntCons(4, IntNil))))) == 4;
{
}
datatype list<A> = Nil | Cons(head: A, tail: list)
ghost function size(l: list): nat
{
  if (l.Nil?) then 0 else 1+size(l.tail)
}
ghost function app(a: list, b: list): list
{
  if (a.Nil?) then b else Cons(a.head, app(a.tail, b))
}
ghost method compute_size4()
  ensures size(Cons(1, Cons(2, Cons(3, Cons(4, Nil))))) == 4;
{
}
ghost method compute_size4_cons()
  ensures size(Cons(IntNil, Cons(IntNil, Cons(IntNil, Cons(IntNil, Nil))))) == 4;
{
}
ghost method compute_appsize()
  ensures size(app(Cons(1, Cons(2, Nil)), Cons(3, Cons(4, Nil))))==4;
{
}

datatype exp = Plus(e1: exp, e2: exp) | Num(n: int) | Var(x: int)
ghost function interp(env: map<int,int>, e: exp): int
  decreases e;
{
  if (e.Plus?) then interp(env, e.e1)+interp(env, e.e2)
  else if (e.Num?) then e.n
  else if (e.Var? && e.x in env) then env[e.x]
  else 0
}
ghost method compute_interp1()
  ensures interp(map[], Plus(Plus(Num(1), Num(2)), Plus(Num(3), Num(4))))==10;
{
}
ghost method compute_interp2(env: map<int,int>)
  requires 0 in env && env[0]==10;
  ensures interp(env, Plus(Plus(Var(0), Num(1)), Num(0)))==11;
{
}
ghost method compute_interp3(env: map<int,int>)
  requires 0 in env && env[0]==10 && 1 !in env;
  ensures interp(env, Plus(Var(0), Plus(Var(1), Var(0))))==20;
{
}
ghost function cinterp(env: map<int,int>, e: exp): int
  decreases e;
{
  match e
  case Plus(e1, e2) => cinterp(env, e1)+cinterp(env, e2)
  case Num(n) => n
  case Var(x) => if x in env then env[x] else 0
}
ghost method compute_cinterp1()
  ensures cinterp(map[], Plus(Plus(Num(1), Num(2)), Plus(Num(3), Num(4))))==10;
{
}
ghost method compute_cinterp2(env: map<int,int>)
  requires 0 in env && env[0]==10;
  ensures cinterp(env, Plus(Plus(Var(0), Num(1)), Num(0)))==11;
{
}
ghost method compute_cinterp3(env: map<int,int>)
  requires 0 in env && env[0]==10 && 1 !in env;
  ensures cinterp(env, Plus(Var(0), Plus(Var(1), Var(0))))==20;
{
}

ghost function opt(e: exp): exp
{
  match e
  case Num(n) => e
  case Var(x) => e
  case Plus(e1, e2) =>
    var o1 := opt(e1);
    if (o1.Num? && o1.n==0) then e2 else Plus(o1, e2)
}
ghost method opt_test()
  ensures opt(Plus(Plus(Plus(Num(0), Num(0)), Num(0)), Num(1)))==Num(1);
{
}
ghost function copt(e: exp): exp
{
  match e
  case Num(n) => e
  case Var(x) => e
  case Plus(e1, e2) => match e1
    case Num(n) => if n==0 then e2 else e
    case Var(x) => e
    case Plus(e11, e12) =>
      var o1 := copt(e1);
      if (o1.Num? && o1.n==0) then e2 else Plus(o1, e2)
}
ghost method copt_test()
  ensures copt(Plus(Plus(Plus(Num(0), Num(0)), Num(0)), Num(1)))==Num(1);
{
}

ghost function power(b: int, n: nat): int
{
  if (n==0) then 1 else b*power(b, n-1)
}
ghost method test_power()
  ensures power(power(2, 3), 1+power(2, 2))==32768;
{
}

ghost function fib(n: nat): nat
{
  if (n<2) then n else fib(n-1)+fib(n-2)
}
ghost method test_fib()
  ensures fib(12)==144;
{
}
ghost method test_fib1(k: nat)
  ensures k==12 ==> fib(k)==144;
{
}
ghost method test_fib2(k: nat)
  ensures 12<=k && k<=12 ==> fib(k)==144;
{
}
ghost method test_fib3(k: nat, m: nat)
{
  var y := 12;
  assert y <= k && k < y + m && m == 1 ==> fib(k)==144;
}

module NeedsAllLiteralsAxiom {
  // The following test shows that there exist an example that
  // benefits from the all-literals axiom.  (It's not clear how
  // important such an example is, nor is it clear what the cost
  // of including the all-literals axiom is.)

  ghost function trick(n: nat, m: nat): nat
    decreases n;  // note that m is not included
  {
    if n < m || m==0 then n else trick(n-m, m) + m
  }

  lemma lemma_trick(n: nat, m: nat)
    ensures trick(n, m) == n;
  {
  }

  lemma calc_trick(n: nat, m: nat)
    ensures trick(100, 10) == 100;
  {
  }
}

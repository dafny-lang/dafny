
module QuantReads {

  function All<A>(p : A -> bool) : bool
    reads set x : A, y : object | y in p.reads(x) :: y;
    requires forall x : A :: p.requires(x);
  {
    forall x : A :: p(x)
  }

  lemma AllQuant<A>(p : A -> bool)
    requires All.requires(p);
    requires All(p);
    ensures forall x : A :: p(x);
  {
  }

}

module Forall {

  function All<A>(p : A -> bool) : bool
  {
    forall x :: p.requires(x) && p(x)
  }

  function CallMe(f : int -> int) : int
    requires All(f.requires);
  {
    f(1) + f(2)
  }

}

module Quant {

  function All<A>(p : A -> bool) : bool
    requires forall x : A :: p.requires(x);
  {
    forall x : A :: p(x)
  }

  lemma AllBool(p : bool -> bool)
    requires forall x : bool :: p.requires(x);
    requires All(p);
    ensures p(true) && p(false);
  {
  }

  method Boo()
    requires All(x => x);
    ensures false;
  {
    AllBool(x => x);
  }

  lemma AllQuant<A>(p : A -> bool)
    requires All.requires(p);
    requires All(p);
    ensures forall x : A :: p(x);
  {
  }

  method Boo2()
    requires All(x => x);
    ensures false;
  {
    assert (x => x)(false);
  }


  method Koo(s : set<int>, t : set<int>)
    requires All(x => (x in s ==> x in t) && (x in t ==> x in s));
    ensures All(x => x in s <==> x in t);
  {
  }

}

module ReadAll {

  datatype List<A> = Nil | Cons(A,List<A>);

  function All(p : A -> bool, xs : List) : bool
    reads (set x, y | y in p.reads(x) :: y);
    requires forall x :: p.reads(x) == {} && p.requires(x);
    decreases xs;
  {
    match xs
      case Nil => true
      case Cons(x,xs) => p(x) && All(p,xs)
  }

  function Div(xs : List<int>) : List<int>
    requires All(x => x > 0, xs);
  {
    match xs
      case Nil => Nil
      case Cons(x,xs) => Cons(100 / x,Div(xs))
  }

}

module Requires {

  method SmallTest(f : int -> int)
    requires f.requires(0);
  {
    print f(0);
  }

  datatype List<A> = Nil | Cons(hd: A,tl: List<A>);

  function All<A>(p : A -> bool, xs : List<A>) : bool
    requires forall x :: p.requires(x);
    decreases xs;
  {
    match xs
      case Nil => true
      case Cons(x,xs) => p(x) && All(p,xs)
  }

  function method Map<A,B>(f : A -> B, ys : List<A>) : List<B>
    requires All(f.requires, ys);
    decreases ys;
  {
    match ys
      case Nil => Nil
      case Cons(x,xs) => Cons(f(x),Map(f,xs))
  }

}

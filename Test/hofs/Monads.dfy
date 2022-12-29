// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Monad {
  type M<A>

  function method Return<A>(x: A): M<A>
  function method Bind<A,B>(m: M<A>, f:A -> M<B>): M<B>

  // return x >>= f = f x
  lemma LeftIdentity<A,B>(x: A, f: A -> M<B>)
    ensures Bind(Return(x),f) == f(x)

  // m >>= return = m
  lemma RightIdentity<A>(m: M<A>)
    ensures Bind(m,Return) == m

  // (m >>= f) >>= g = m >>= (x => f(x) >>= g)
  lemma Associativity<A,B,C>(m: M<A>, f: A -> M<B>, g: B -> M<C>)
    ensures Bind(Bind(m,f),g) ==
            Bind(m,x => Bind(f(x),g))
}

module Identity refines Monad {
  datatype M<A> = I(A)

  function method Return<A>(x: A): M<A>
  { I(x) }

  function method Bind<A,B>(m: M<A>, f:A -> M<B>): M<B>
  {
    var I(x) := m; f(x)
  }

  lemma LeftIdentity<A,B>(x: A, f: A -> M<B>)
  {
  }

  lemma RightIdentity<A>(m: M<A>)
  {
    assert Bind(m,Return) == m;
  }

  lemma Associativity<A,B,C>(m: M<A>, f: A -> M<B>, g: B -> M<C>)
  {
    assert
      Bind(Bind(m,f),g) ==
      Bind(m,x => Bind(f(x),g));
  }

}

module Maybe refines Monad {
  datatype M<A> = Just(A) | Nothing

  function method Return<A>(x: A): M<A>
  { Just(x) }

  function method Bind<A,B>(m: M<A>, f:A -> M<B>): M<B>
  {
    match m
    case Nothing => Nothing
    case Just(x) => f(x)
  }

  lemma LeftIdentity<A,B>(x: A, f: A -> M<B>)
  {
  }

  lemma RightIdentity<A>(m: M<A>)
  {
    assert Bind(m,Return) == m;
  }

  lemma Associativity<A,B,C>(m: M<A>, f: A -> M<B>, g: B -> M<C>)
  {
    assert
      Bind(Bind(m,f),g) ==
      Bind(m,x => Bind(f(x),g));
  }

}

module List refines Monad {
  datatype M<A> = Cons(hd: A,tl: M<A>) | Nil

  function method Return<A>(x: A): M<A>
  { Cons(x,Nil) }

  function method Concat<A>(xs: M<A>, ys: M<A>): M<A>
  {
    match xs
    case Nil => ys
    case Cons(x,xs) => Cons(x,Concat(xs,ys))
  }

  function method Join<A>(xss: M<M<A>>): M<A>
  {
    match xss
    case Nil => Nil
    case Cons(xs,xss) => Concat(xs,Join(xss))
  }

  function method Map<A,B>(xs: M<A>, f: A -> B): M<B>
  {
    match xs
    case Nil => Nil
    case Cons(x,xs) => Cons(f(x),Map(xs,f))
  }

  function method Bind<A,B>(m: M<A>, f: A -> M<B>): M<B>
  {
    Join(Map(m,f))
  }

  lemma LeftIdentity<A,B>(x: A, f: A -> M<B>)
  {
    calc {
       Bind(Return(x),f);
    == Join(Map(Cons(x,Nil),f));
    == Join(Cons(f(x),Nil));
    == Concat(f(x),Nil);
    == { assert forall xs: M<B> {:induction} :: Concat(xs,Nil) == xs; }
       f(x);
    }
  }

  lemma RightIdentity<A>(m: M<A>)
  {
    match m
    case Nil =>
      calc {
         Bind(Nil,Return);
      == Join(Map(Nil,Return));
      == Join(Nil);
      == Nil;
      == m;
      }
    case Cons(x,xs) =>
      calc {
         Bind(m,Return);
      == Bind(Cons(x,xs),Return);
      == Join(Map(Cons(x,xs),Return));
      == Join(Cons(Return(x),Map(xs,Return)));
      == Concat(Return(x),Join(Map(xs,Return)));
      == { RightIdentity(xs); }
         Concat(Return(x),xs);
      == Concat(Cons(x,Nil),xs);
      == Cons(x,xs);
      == m;
      }
  }

  lemma ConcatAssociativity<A>(xs: M<A>, ys: M<A>, zs: M<A>)
    ensures Concat(Concat(xs,ys),zs) == Concat(xs,Concat(ys,zs));
  {}

  lemma BindMorphism<A,B>(xs: M<A>, ys: M<A>, f: A -> M<B>)
    ensures Bind(Concat(xs,ys),f) == Concat(Bind(xs,f),Bind(ys,f));
  {
    match xs
    case Nil =>
      calc {
         Bind(Concat(Nil,ys),f);
      == Bind(ys,f);
      == Concat(Nil,Bind(ys,f));
      == Concat(Bind(Nil,f),Bind(ys,f));
      }
    case Cons(z,zs) =>
      calc {
         Bind(Concat(xs,ys),f);
      == Bind(Concat(Cons(z,zs),ys),f);
      == Concat(f(z),Bind(Concat(zs,ys),f));
      == { BindMorphism(zs,ys,f); }
         Concat(f(z),Concat(Bind(zs,f),Bind(ys,f)));
      == { ConcatAssociativity(f(z),Bind(zs,f),Bind(ys,f)); }
         Concat(Concat(f(z),Join(Map(zs,f))),Bind(ys,f));
      == Concat(Bind(Cons(z,zs),f),Bind(ys,f));
      == Concat(Bind(xs,f),Bind(ys,f));
      }
  }

  lemma Associativity<A,B,C>(m: M<A>, f: A -> M<B>, g: B -> M<C>)
  {
    match m
    case Nil =>
      calc {
         Bind(Bind(m,f),g);
      == Bind(Bind(Nil,f),g);
      == Bind(Nil,g);
      == Nil;
      == Bind(Nil,x => Bind(f(x),g));
      == Bind(m,x => Bind(f(x),g));
      }
    case Cons(x,xs) =>
      calc {
         Bind(Bind(m,f),g);
      == Bind(Bind(Cons(x,xs),f),g);
      == Bind(Concat(f(x),Bind(xs,f)),g);
      == { BindMorphism(f(x),Bind(xs,f),g); }
         Concat(Bind(f(x),g),Bind(Bind(xs,f),g));
      == { Associativity(xs,f,g); }
         Concat(Bind(f(x),g),Join(Map(xs,y => Bind(f(y),g))));
      == Join(Cons(Bind(f(x),g),Map(xs,y => Bind(f(y),g))));
      == Join(Map(Cons(x,xs),y => Bind(f(y),g)));
      == Bind(Cons(x,xs),y => Bind(f(y),g));
      == Bind(m,x => Bind(f(x),g));
      }
  }
}

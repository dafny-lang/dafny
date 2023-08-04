// RUN: %dafny /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module Monad {
  type M<A>

  function Return<A>(x: A): M<A>
  function Bind<A,B>(m: M<A>, f:A -> M<B>): M<B>

  // return x >>= f = f x
  lemma LeftIdentity<A,B>(x : A, f : A -> M<B>)
    ensures Bind(Return(x),f) == f(x)

  // m >>= return = m
  lemma RightIdentity<A>(m : M<A>)
    ensures Bind(m, x => Return(x)) == m // problem: can't prove it for Bind(m, Return)

  // (m >>= f) >>= g = m >>= (x => f(x) >>= g)
  lemma Associativity<A,B,C>(m : M<A>, f:A -> M<B>, g: B -> M<C>)
    ensures Bind(Bind(m,f),g) ==
            Bind(m,x => Bind(f(x),g))
}

module State refines Monad {
//   type S // doesn't work because S is used left of an arrow
  datatype M<A> = State(runState: int -> (A, int))

  function Return<A>(x: A): M<A>
  { State(s => (x, s)) }

  function Bind<A,B>(m: M<A>, f:A -> M<B>): M<B>
  {
    match m case State(h) =>
      State(s =>
            match h(s) case (a, newState) =>
              match f(a) case State(g) => g(newState))
  }

  lemma {:axiom} FunEq<X, Y>(f: X -> Y, g: X -> Y)
    requires forall x :: f(x) == g(x)
    ensures f == g

  lemma LeftIdentity<A,B>(x : A, f : A -> M<B>)
    ensures Bind(Return(x), f) == f(x)
  {
      var State(h) := State(s => (x, s));
      var State(g2) := f(x);
      calc {
          Bind(Return(x), f);
      ==
          Bind(State(s => (x, s)), f);
      ==
          State(s =>
                match ((s => (x, s))(s))
                case (a, newState) =>
                  match f(a) case State(g) =>
                    g(newState));
      == {
            FunEq(s =>
                    match ((s => (x, s))(s))
                    case (a, newState) =>
                      match f(a)
                      case State(g) => g(newState),
                  s =>
                    match (x, s)
                    case (a, newState) =>
                      match f(a)
                      case State(g) => g(newState));
         }
          State(s =>
                  match (x, s) case (a, newState) =>
                    match f(a) case State(g) =>
                      g(newState));
      == {
            FunEq((s =>
                    match (x, s) case (a, newState) =>
                      match f(a) case State(g) => g(newState)),
                  (s => match f(x) case State(g) => g(s)));
         }
          State(s => match f(x) case State(g) => g(s));
      == { FunEq(s => match f(x) case State(g) => g(s), g2); }
          State(g2);
      ==
          f(x);
    }
  }

  lemma RightIdentity<A>(m : M<A>)
  {
      match m case State(h) =>
        calc {
          Bind(m, x => Return(x));
        ==
          State(s =>
                  match h(s) case (a, newState) =>
                    match (x => Return(x))(a)
                    case State(g) => g(newState));
        == {
            FunEq((s =>
                    match h(s) case (a, newState) =>
                      match (x => Return(x))(a) case State(g) => g(newState)),
                  (s => h(s)));
          }
          State(s => h(s));
        == { FunEq(s => h(s), h); }
          State(h);
        ==
          m;
        }
  }

  lemma Associativity<A,B,C>(m : M<A>, f:A -> M<B>, g: B -> M<C>)
    ensures Bind(Bind(m, f), g) == Bind(m, x => Bind(f(x), g))
  {
    match m case State(h) =>
        calc {
          Bind(Bind(m, f), g);
        ==
          match Bind(m, f) case State(h1) =>
            State(s =>
                    match h1(s) case (a, newState) =>
                      match g(a) case State(h1) =>
                        h1(newState));
        ==
          match (State(s =>
                        match h(s) case (a, newState) =>
                          match f(a) case State(g2) => g2(newState)))
          case State(h1) =>
            State(s =>
                    match h1(s) case (a, newState) =>
                      match g(a) case State(h1) =>
                        h1(newState));
        ==
          State(s =>
                  match (s => match h(s) case (a, newState) => match f(a) case State(g2) => g2(newState))(s)
                  case (a, newState) =>
                    match g(a) case State(h1) =>
                      h1(newState));
        == {
              FunEq(s =>
                      match (s => match h(s) case (a, newState) => match f(a) case State(g2) => g2(newState))(s)
                      case (a, newState) =>
                        match g(a) case State(h1) =>
                          h1(newState),
                    s =>
                      match (match h(s) case (a, newState) => match f(a) case State(g2) => g2(newState))
                      case (a, newState) =>
                        match g(a) case State(h1) =>
                          h1(newState));
           }
          State(s =>
                  match (match h(s) case (a, newState) => match f(a) case State(g2) => g2(newState))
                  case (a, newState) =>
                    match g(a) case State(h1) =>
                      h1(newState));
        ==
	{ /* OS: Added for PM */
             FunEq(s =>
                      match (match h(s) case (a, newState) => match f(a) case State(g2) => g2(newState))
                      case (a, newState) =>
                        match g(a) case State(h1) =>
                          h1(newState),
		  s => match h(s) case (a, newState) =>
                    match f(a) case State(g2) =>
                      match g2(newState) case (b, newState2) =>
                          match g(b) case State(h1) =>
                            h1(newState2));
           }
          State(s =>
                  match h(s) case (a, newState) =>
                    match f(a) case State(g2) =>
                      match g2(newState) case (b, newState2) =>
                          match g(b) case State(h1) =>
                            h1(newState2));
      }

      calc {
        Bind(m, x => Bind(f(x), g));
      ==
        Bind(State(h), x => Bind(f(x), g));
      ==
        State(s =>
                match h(s) case (a, newState) =>
                  match (x => Bind(f(x), g))(a) case State(g2) =>
                    g2(newState));
      == {
            FunEq(s => match h(s) case (a, newState) => match (x => Bind(f(x), g))(a) case State(g2) => g2(newState),
                  s => match h(s) case (a, newState) => match Bind(f(a), g) case State(g2) => g2(newState));
         }
        State(s =>
                match h(s) case (a, newState) =>
                  match Bind(f(a), g) case State(g2) =>
                    g2(newState));
      == {
            FunEq((s => match h(s) case (a, newState) => match Bind(f(a), g) case State(g2) => g2(newState)),
                  (s => match h(s) case (a, newState) =>
                    match (match f(a) case State(h2) =>
                            State(s =>
                                  match h2(s) case (a2, newState2) =>
                                    match g(a2) case State(g2) => g2(newState2)))
                    case State(g3) =>
                      g3(newState)));
         }
        State(s =>
                match h(s) case (a, newState) =>
                  match (match f(a) case State(h2) =>
                          State(s =>
                                match h2(s) case (a2, newState2) =>
                                  match g(a2) case State(g2) => g2(newState2)))
                  case State(g3) =>
                    g3(newState));
      == { /* OS: Added for PM */
            FunEq(s => match h(s) case (a, newState) =>
                    match (match f(a) case State(h2) =>
                            State(s =>
                                  match h2(s) case (a2, newState2) =>
                                    match g(a2) case State(g2) => g2(newState2)))
                    case State(g3) =>
                      g3(newState),
		   s =>
                match h(s) case (a, newState) =>
                  match f(a) case State(h2) =>
                      match State(s => match h2(s) case (a2, newState2) =>
                                        match g(a2) case State(g2) => g2(newState2))
                      case State(g3) =>
                        g3(newState));
         }
        State(s =>
                match h(s) case (a, newState) =>
                  match f(a) case State(h2) =>
                      match State(s => match h2(s) case (a2, newState2) =>
                                        match g(a2) case State(g2) => g2(newState2))
                      case State(g3) =>
                        g3(newState));
      == { FunEq(s => match h(s) case (a, newState) =>
                        match f(a) case State(h2) =>
                          match State(s => match h2(s) case (a2, newState2) =>
                            match g(a2) case State(g2) =>
                              g2(newState2)) case State(g3) =>
                                g3(newState),
                   s => match h(s) case (a, newState) =>
                          match f(a) case State(h2) =>
                            (s => match h2(s) case (a2, newState2) =>
                              match g(a2) case State(g2) =>
                                g2(newState2))(newState));
         }
        State(s =>
                match h(s) case (a, newState) =>
                  match f(a) case State(h2) =>
                    (s => match h2(s) case (a2, newState2) =>
                            match g(a2) case State(g2) => g2(newState2))(newState));
      == {
            FunEq(s => match h(s) case (a, newState) =>
                        match f(a) case State(h2) =>
                 (s => match h2(s) case (a2, newState2) =>
                        match g(a2) case State(g2) =>
                          g2(newState2))(newState),
                  s => match h(s) case (a, newState) =>
                        match f(a) case State(h2) =>
                          match h2(newState) case (a2, newState2) =>
                            match g(a2) case State(g2) =>
                              g2(newState2));
         }
        State(s =>
                match h(s) case (a, newState) =>
                  match f(a) case State(h2) =>
                    match h2(newState) case (a2, newState2) =>
                      match g(a2) case State(g2) =>
                        g2(newState2));
      }
  }
}

// RUN: %exits-with 2 %dafny /compile:0 /allocated:4 /functionSyntax:4 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Resolution (for verification, see git-issue-19b.dfy)

module M0 {
  // This is the original example from Issue 19. It has been fixed by the resolution
  // check that forbids functions that would depend on the allocation state.

  ghost predicate P<T>(x: T)

  ghost predicate AllP<T>() { forall x :: P<T>(x) } // error: predicate is not allowed to depend on allocation state

  class C {}

  method M1()

  method M2()
  {
    assume (forall x :: P<C>(x));
    M1();
    assert (forall x :: P<C>(x));
  }

  method M3()
  {
    assume (forall x :: P<C>(x));
    M1();
    assert AllP<C>();
    assert (forall x :: P<C>(x));
  }
}

module M1 {
  ghost predicate P<T>(x:T)

  ghost predicate AllP<T(!new)>() { forall x :: P<T>(x) } // note, declares T(!new)

  class C {}

  method M1()

  method M2()
  {
    assume (forall x :: P<C>(x));
    M1();
    assert (forall x :: P<C>(x));
  }

  method M3()
  {
    assume (forall x :: P<C>(x));
    M1();
    assert AllP<C>(); // error: C cannot be passed in for a !new type
    assert (forall x :: P<C>(x));
  }
}

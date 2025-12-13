// RUN: %exits-with 2 %verify --allow-axioms "%s" > "%t"
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
    assume forall x :: P<C>(x);
    M1();
    assert forall x :: P<C>(x);
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
  ghost predicate P<T>(x: T)

  ghost predicate AllP<T(!new)>() { forall x :: P<T>(x) } // note, declares T(!new)

  class C {}

  method M1()

  method M2()
  {
    assume forall x :: P<C>(x);
    M1();
    assert forall x :: P<C>(x);
  }

  method M3()
  {
    assume forall x :: P<C>(x);
    M1();
    assert AllP<C>(); // error: C cannot be passed in for a !new type
    assert forall x :: P<C>(x);
  }
}

module M200 {
  ghost predicate P<T>(x: T)

  ghost predicate AllP<T>()
    reads **
  { forall x :: P<T>(x) }

  class C {}

  method M1()

  method M2()
  {
    assume forall x :: P<C>(x);
    M1();
    assert forall x :: P<C>(x); // no issue with resolution here (but verifier will complain, see git-issue-19b.dfy)
  }

  method M3()
  {
    assume forall x :: P<C>(x);
    M1();
    assert AllP<C>(); // no issue with resolution here (but verifier will complain, see git-issue-19b.dfy)
    assert forall x :: P<C>(x);
  }

  // a more concrete test

  class Cell { var data: int }

  ghost predicate Always100()
    reads **
  {
    forall c: Cell :: c.data == 100
  }

  lemma Lemma() {
  }

  method AMethodIsAMethod() {
    var c := new Cell;
    c.data := 101;
  }

  method TestStarStar()
    requires Always100()
  {
    Lemma();
    assert Always100(); // yes, nothing in the state has changed so far
    AMethodIsAMethod();
    assert Always100(); // no issue with resolution here (but verifier will complain, see git-issue-19b.dfy)
  }

  function DirectUseOfAllocated(c: Cell): int
  {
    if allocated(c) then 3 else 4 // error: function not allowed to depend on allocation state, so cannot syntactically use `allocated`
  }

  function DirectUseOfAllocatedWithStarStar(c: Cell): int
    reads **
  {
    if allocated(c) then 3 else 4 // fine, because of the `reads **`
  }
}

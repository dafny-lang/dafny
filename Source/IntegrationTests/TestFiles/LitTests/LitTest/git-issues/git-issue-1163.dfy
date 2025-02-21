// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"


ghost function F(i: int): int

method M() {
  ghost var f := old(i => F(i));  // the translation of this once had crashed the verifier (warning: old has no effect)
}

class MyClass {
  var y: int

  method N()
    modifies this
  {
    y := 8;
    label L:
    var p := new MyClass;
    label K:
    if * {
      ghost var g := old@L((x: int) reads p.R(this) => x);  // error, because p is not allocated in L
    } else if * {
      ghost var g := old@L((x: int) reads R(p) => x);  // error, because p is not allocated in L
    } else if * {
      ghost var g := old@K((x: int) reads p.R(p) => x);
    } else {
      ghost var g := old((x: int) reads p.R(p) => x);  // error, because p is not allocated in old state
    }
  }

  method O()
    modifies this
  {
    y := 8;
    label L:
    ghost var h :=
      old@L(
        (p: MyClass) requires p.y == 10 reads p =>
        assert p.y == 10; 5  // this assert once didn't work, because of a mismatch of heap variables in the translator
      );
  }

  method Q(q: MyClass)
    requires R(this) != q
    modifies this
  {
    // The following uses of p in R(p) should be allowed. In particular, they should not
    // produce "p not allocated in function state" errors.
    if * {
      ghost var h := old((p: MyClass) reads R(p) => 5);
    } else if * {
      ghost var s := old(iset p: MyClass | R(p) == p);
      assert s == iset{this};
    } else if * {
      ghost var m := old(imap p: MyClass | R(p) == p :: 12);
      assert m == imap[this := 12];
    } else if * {
      ghost var m := old(var p: MyClass :| R(p) == p; p.y);
      assert m == y;
    } else {
      ghost var m := old(forall p: MyClass :: R(p) == p);
      assert !m by {
        assert this.R(q) != q;
      }
    }
  }

  method SuchThat(q: MyClass)
    requires R(q) == this
  {
    if
    case q == this =>
      ghost var m := var p: MyClass :| this.R(p) == p; p.y;
      assert m == y;
    case true =>
      // To prove the existence of a "p" like in the next line, there must, first off, be a term
      // of the form "_.R(this)" to trigger the quantifier. There is no such term hanging around,
      // so this proof obligation fails.
      ghost var m := var p: MyClass :| p.R(this) == p; p.y; // error: cannot find witness
    case true =>
      // Here, there is one term of the form "this.R(_)", namely "q". Alas, "this == q" may not
      // hold, so this proof obligation fails.
      ghost var m := var p: MyClass :| this.R(p) == p; p.y; // error: cannot find witness
    case true =>
      ghost var th := R(this);
      // This is the same such-that expression as in the previous case. Here, the presence of
      // the term "R(this)" triggers the quantifier with "this", and thus the such-that proof
      // obligation succeeds.
      ghost var m := var p: MyClass :| this.R(p) == p; p.y;
  }

  ghost function R(c: MyClass): MyClass
    reads this
  {
    this
  }
}

// RUN: %exits-with 4 %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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

  method Q()
    modifies this
  {
    // The following uses of p in R(p) should be allowed. In particular, they should not
    // produce "p not allocated in function state" errors.
    if * {
      ghost var h := old((p: MyClass) reads R(p) => 5);
    } else if * {
      ghost var s := old(iset p: MyClass | R(p) == p);
    } else if * {
      ghost var m := old(imap p: MyClass | R(p) == p :: 12);
    } else if * {
      ghost var m := old(var p: MyClass :| R(p) == p; p.y);
    } else {
      ghost var m := old(forall p: MyClass :: R(p) == p);
    }
  }

  ghost function R(c: MyClass): MyClass
    reads this
  {
    this
  }
}

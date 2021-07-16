// RUN: %dafny /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var x: int
  var z: int

  method M()
    requires x == 6
    modifies this
  {
    x := 10;
    label 00:
    label 01:
    x := x + 1;
    label 2:
    {
      label 0_2:
      x := x + 1;
      label 3:
      assert true;
    }
    label 0003:
    x := x + 1;
    label four:
    x := x + 1;
    assert old(x) == 6;

    assert old@00(x) == old@01(x) == 10;
    assert old@2(x) == old@0_2(x) == 11;
    assert old@3(x) == 12 == old@0003(x);
    assert old@four(x) == 13;
    assert x == 14;
    assert x == old(x);  // error: (just to check that not everything is provable)
  }

  method Lets(i: int, whoKnows: bool) returns (o: int)
    requires x == i == 10
    modifies this
    ensures 4*o == 24
  {
    x := x + 3;
    label 7:  // x == 13
    x := x + 5;
    o := i - 4;
    assert o == var six :| six == 6; six;
    label L8:  // x == 18
    x := 2;
    ghost var k :| k == x + old(x) + old@7(x) + old@L8(x);  // assign such that
    assert k == 2 + 10 + 13 + 18;
    ghost var m :=
      var k :| k == x + old(x) + old@7(x) + old@L8(x); k;  // let such that
    assert m == 2 + 10 + 13 + 18;
    assert o == var six :| six == 6; six;
    assert o == 18 - var twelve :| twelve == 12; twelve;
    assert whoKnows;  // error: no evidence that it holds (or doesn't hold)
  }

  method Unchanged(y: int, c: C, d: C)
    modifies this, c, d
  {
    if y < 5 {
      x := x + 1;
      assert c != this ==> unchanged(c);
    } else {
      c.x := c.x + 2;
      assert c != this ==> unchanged(this);
    }
    label Middle:
    d.x := d.x + 1;
    label End:
    if
    case d != this && d != c =>
      assert unchanged@Middle(this, c);
    case d != this =>
      assert unchanged@Middle(`x);
    case d != c =>
      assert unchanged@Middle(`x);  // error: the value of this.x may indeed have changed
    case d != c =>
      assert unchanged@Middle({c});
      assert unchanged@Middle({this,d}`z);
      assert unchanged({this,d}`z);
    case true =>
      assert unchanged@End({c,d});
  }

  method Fresh(y: int, b: bool)
    modifies this
  {
    label Start:
    var c := new C;
    if b {
      c := this;
    }
    if y < 5 {
      assert c != this ==> fresh(c);
    } else {
      c.x := c.x + 2;
      assert c != this ==> fresh(c);
    }
    label Middle:
    var d := new C;
    label End:
    if
    case true =>
      assert fresh(d);
    case true =>
      assert fresh@Middle(d);
    case true =>
      assert fresh@End(d); // error: d is not fresh since End
    case true =>
      assert fresh@Middle(c); // error: c is not fresh since Middle
    case true =>
      var e := d;
      assert fresh@Middle(e);
      assert fresh@End(e); // error: e is not fresh since End
    case true =>
      assert fresh@Start(c); // error: c might be this
    case true =>
      assert b || fresh@Start(c);
  }

  var cc: C?

  method FreshAgain(b: bool)
    requires cc != null
    modifies this
  {
    label A:
    if b {
      cc := new C;
    }
    label B:
    if
    case true =>
      assert cc == old(cc) || fresh@A(cc);
    case b =>
      assert fresh@A(cc);
    case b =>
      assert fresh@B(cc); // error: cc is never an object allocated after B
    case b =>
      assert fresh@A(old(cc)); // error: original value of cc is not fresh since A
    case b =>
      assert fresh@A(old@B(cc));
  }

  method DefinednessOld(m: C?, arr: array<int>)
    requires this.cc == m != null && arr.Length == 100
    modifies this
  {
    label Start:
    var n := new C;
    n.cc := this;
    this.cc := n;
    var brr := new int[120];
    label End:
    if
    // ----- old ----- (any dereference must be of object allocated in the specified old state)
    case true =>
      assert old@Start(n) == n; // "old" has no effect on local variables
      assert old@Start(this.cc) == m;
      assert old@Start(this.cc.x) == m.x;
    case true =>
      var u := old(n.x); // error: n is not allocated in old state
    case true =>
      var u := old@Start(n.x); // error: n is not allocated in old state
    case true =>
      var u := old@End(n.x);
      assert u == this.cc.x;
    case true =>
      var a := old(arr[0]);
      a := old@Start(arr[0]);
      a := old@End(arr[0]);
    case true =>
      var a := old(brr[0]); // error: brr is not allocated in old state
    case true =>
      var a := old@Start(brr[0]); // error: brr is not allocated in Start state
    case true =>
      var a := old@End(brr[0]);
  }

  method DefinednessUnchanged(m: C?, s: set<C>)
    requires this.cc == m != null
    modifies this
  {
    label Start:
    var n := new C;
    n.cc := this;
    this.cc := n;
    var s' := s + {n};
    label End:
    if
    // ----- unchanged ----- (any object mentioned must be allocated in the specified old state)
    case true =>
      var v := unchanged(n); // error: n is not allocated in old state
    case true =>
      var v := unchanged@Start(n); // error: n is not allocated in Start state
    case true =>
      var v := unchanged@End(n);
      assert v;
      assert unchanged@End(this.cc);
      cc.x := cc.x + 1;
      assert !unchanged@End(n);
    case true =>
      assert this in s || unchanged@Start(s);
    case true =>
      var v := unchanged@Start(s'); // error: not every object is s' was allocated in Start state
  }

  method DefinednessFresh(m: C?)
    requires this.cc == m != null
    modifies this
  {
    label Start:
    var n := new C;
    n.cc := this;
    this.cc := n;
    var brr := new int[120];
    label End:
    if
    // ----- fresh ----- (argument has no allocatedness restrictions)
    case true =>
      assert !fresh(n.cc); // n.cc == this
      assert !fresh@Start(n.cc);
      assert !fresh@End(n.cc);
    case true =>
      assert old@Start(this.cc) == m;
      assert !fresh@End(old@Start(this.cc));
      assert old@End(this.cc) == n;
      assert fresh@Start(old@End(this.cc));
  }

  twostate function FOld(c: C, new c': C): bool {
    && old(x) == 3
    && old(c.x) == 3
    && old(c'.x) == 3 // error: c' is not allocated in old state
  }

  twostate function FUnchanged(x: int, c: C, new c': C, s: set<C>, new s': set<C>): bool {
    && unchanged(this)
    && unchanged(c)
    && (x == 7 ==> unchanged(c')) // error: c' is not allocated in old state
    && unchanged(s)
    && (x == 9 ==> unchanged(s')) // error: s' is not allocated in old state
  }

  twostate function FFresh(c: C, new c': C): bool {
    && fresh(this)
    && fresh(c)
    && fresh(c')
  }
}

twostate predicate M0(u: C, s: set<C>, t: seq<C>) {
  && unchanged(u)
  && unchanged(s)
  && unchanged(t)
}
twostate predicate M1(u: C?, s: set<C?>, t: seq<C?>) {
  && unchanged(u) // error: may be null
  && unchanged(s) // error: may be null
  && unchanged(t) // error: may be null
}

twostate predicate N0(new u: C, new s: set<C>, new t: seq<C>) {
  && unchanged(u) // error: may not be allocated in old
  && unchanged(s) // error: may not be allocated in old
  && unchanged(t) // error: may not be allocated in old
}
twostate predicate N1(new u: C?, new s: set<C?>, new t: seq<C?>) {
  && unchanged(u) // error (x2): may be null, may not be allocated in old
}
twostate predicate N2(new u: C?, new s: set<C?>, new t: seq<C?>) {
  && unchanged(s) // error (x2): may be null, may not be allocated in old
}
twostate predicate N3(new u: C?, new s: set<C?>, new t: seq<C?>) {
  && unchanged(t) // error (x2): may be null, may not be allocated in old
}

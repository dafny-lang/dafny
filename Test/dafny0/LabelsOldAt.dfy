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
}

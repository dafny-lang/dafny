// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var c, d := new A, new A;
  L(c, d);  // error: 'c' is not old
}

twostate lemma L(c: A, new d: A)
{
  var x := old(c.f);
  var y := old(d.f);  // error: trying to use new 'd' in previous state
}

class A {
  var f: int
  var g: A?

  function GimmieF(): int
    reads this
  {
    f
  }

  twostate lemma L1(other: A) returns (res: bool)
    requires unchanged(this)
    ensures res ==> this == other
  {
    res := this == other;
  }

  twostate lemma L2(a: A, b: A)
    requires old(a != b)
  {}

  twostate lemma L3(a: A, new b: A)
    requires old(a.f != b.f)  // error: b might not exist in the old state
  {}

  twostate lemma L3_and_a_half(a: A, new b: A)
    requires old(a.GimmieF() == b.GimmieF())  // error: b might not exist in old state
  {}

  twostate lemma L4(new a: A)
    requires old(allocated(a)) && unchanged(a)
  {
    assert a.f == old(a.f);
    assert a.GimmieF() == old(a.GimmieF());  // we get that everything about a, including its allocatedness,
                                             // is the same in the previous and current states
  }

  method M4()
  {
    var a := new A;
    if * {
      assert a.f == old(a.f);  // error: a was not allocated initial state
    } else {
      assert a.GimmieF() == old(a.GimmieF());  // error: a was not allocated initial state
    }
  }

  twostate lemma L5(new a: A, new b: A)
  {}

  twostate lemma L6(a: A)
    requires unchanged(a)
  {
    assert a.f == old(a.f);
    assert a.GimmieF() == old(a.GimmieF());
  }

  twostate lemma L7(a: A)
  {
    assert a.f == old(a.f);  // error: state need not agree on a.f
  }
}

class Node {
  var x: int
  var next: Node?
  ghost var Repr: set<Node>
  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    (next != null ==> next in Repr && next.Repr <= Repr && this !in next.Repr && next.Valid())
  }
  constructor (y: int)
    ensures Valid() && fresh(Repr)
  {
    x, next := y, null;
    Repr := {this};
  }
  constructor Prepend(y: int, nxt: Node)
    requires nxt.Valid()
    ensures Valid() && fresh(Repr - nxt.Repr)
  {
    x, next := y, nxt;
    Repr := {this} + nxt.Repr;
  }

  function method Sum(): int
    requires Valid()
    reads Repr
  {
    if next == null then x else x + next.Sum()
  }

  method M(node: Node)
    requires Valid()
    modifies node
    ensures Valid()
  {
    var s := Sum();
    node.x := node.x + 1;
    M_Lemma(node);
    assert s <= Sum();
  }

  twostate lemma M_Lemma(node: Node)
    requires old(Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires unchanged(old(Repr) - {node})
    ensures Valid() && old(Sum()) <= Sum()
    decreases Repr
  {
    if next != null {
      next.M_Lemma(node);
    }
  }

  static twostate lemma M_Lemma_Static(self: Node, node: Node)
    requires old(self.Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires unchanged(old(self.Repr) - {node})
    ensures self.Valid() && old(self.Sum()) <= self.Sum()
    decreases self.Repr
  {
    if self.next != null {
      M_Lemma_Static(self.next, node);
    }
  }

  static twostate lemma M_Lemma_Forall(self: Node, node: Node)
    requires old(self.Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires unchanged(old(self.Repr) - {node})
    ensures self.Valid() && old(self.Sum()) <= self.Sum()
    decreases self.Repr
  {
    forall n: Node | old(allocated(n)) && old(n.Repr < self.Repr && n.Valid())
      ensures n.Valid() && old(n.Sum()) <= n.Sum()
    {
      M_Lemma_Forall(n, node);
    }
    var n := self.next;
    if n != null {
      assert old(allocated(n)) && old(n.Repr < self.Repr && n.Valid());
      assert n.Valid() && old(n.Sum()) <= n.Sum();
    }
  }

  twostate lemma M_Lemma_Alt(node: Node)
    requires old(Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires forall n :: n in old(Repr) && n != node ==> n.x == old(n.x) && n.next == old(n.next) && n.Repr == old(n.Repr)
    ensures Valid() && old(Sum()) <= Sum()
    decreases Repr
  {
    if next != null {
      next.M_Lemma_Alt(node);
    }
  }

  static twostate lemma M_Lemma_Alt_Static(self: Node, node: Node)
    requires old(self.Valid())
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires forall n :: n in old(self.Repr) && n != node ==> n.x == old(n.x) && n.next == old(n.next) && n.Repr == old(n.Repr)
    ensures self.Valid() && old(self.Sum()) <= self.Sum()
    decreases self.Repr
  {
    if self.next != null {
      M_Lemma_Alt_Static(self.next, node);
    }
  }
}

class {:autocontracts} NodeAuto {
  var x: int
  var next: NodeAuto?
  constructor (y: int)
  {
    x, next := y, null;
  }
  constructor {:autocontracts false} Prepend(y: int, nxt: NodeAuto)
    requires nxt.Valid()
    ensures Valid() && fresh(Repr - nxt.Repr)
  {
    x, next := y, nxt;
    Repr := {this} + nxt.Repr;
  }

  function method Sum(): int
  {
    if next == null then x else x + next.Sum()
  }

  method M(node: NodeAuto)
    modifies node
  {
    var s := Sum();
    node.x := node.x + 1;
    M_Lemma(node);
    assert s <= Sum();
  }

  twostate lemma M_Lemma(node: NodeAuto)
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires unchanged(old(Repr) - {node})
    ensures Valid() && old(Sum()) <= Sum()
    decreases Repr
  {
    if next != null {
      next.M_Lemma(node);
    }
  }

  twostate lemma M_Lemma_Alt(node: NodeAuto)
    requires old(node.x) <= node.x && old((node.next, node.Repr)) == (node.next, node.Repr)
    requires forall n: NodeAuto :: n in old(Repr) && n != node ==> n.x == old(n.x) && n.next == old(n.next) && n.Repr == old(n.Repr)
    ensures Valid() && old(Sum()) <= Sum()
    decreases Repr
  {
    if next != null {
      next.M_Lemma_Alt(node);
    }
  }
}

module TwoStateAt {
  class Cell {
    var data: int
    constructor (x: int)
      ensures data == x
    {
      data := x;
    }

    static twostate function Sum<Y>(c: Cell, y: Y): int
      reads c
    {
      c.Plus<Y>(y)
    }

    twostate function Plus<Y>(y: Y): int
      reads this
    {
      SP<Y>(this, y)
    }

    twostate lemma LL<Y>(y: Y)
      ensures old(data) < data
    {
      if old(data) < data {
        // we're good
      } else if old(data) != data {
        // the following lemma call will let us prove anything
        IdentityLemma(this, y);
        assert false;
      } else {  // error: postcondition doesn't hold on this path
      }
    }

    static twostate lemma IdentityLemma<Y>(c: Cell, y: Y)
      ensures old(c.data) == c.data
    {  // error: postcondition does not hold
    }
  }

  twostate function SP<Y>(c: Cell, y: Y): int
    reads c
  {
    old(c.data) + c.data
  }

  method Test<Y>(c: Cell, b: bool, y: Y)
    requires c.data == 2
    modifies c
  {
    assert c.Plus(y) == 4;
    c.data := c.data + 3;  // 5
    label Five:
    assert Cell.Sum(c, y) == 7;
    assert Cell.Sum@Five(c, y) == 10;

    c.data := c.data + 1;  // 6
    assert SP(c, y) == 8;
    assert SP@Five(c, 0 as bv3) == 11;

    if b {
      c.data := c.data + 10;  // 16
    } else {
      c.data := c.data + 20;  // 26
    }
    label PostIf:

    assert c.Plus@Five(y) == 21 || c.Plus@Five(0) == 31;
    assert b ==> (var w := Cell.Sum@PostIf(c, y); w) == 32;
    assert !b ==> SP@PostIf(c, y) == 52;
    ghost var u := SP@Five(c, 0);
    assert b ==> u == 21;
    assert !b ==> Cell.Sum@Five(c, y) == 30;  // error: it is 31
  }

  twostate lemma TwoLemma<Y>(c: Cell, y: Y)
    requires 2 * old(c.data) <= Cell.Sum(c, 0)  // tantamount to old(c.data) <= c.data
    ensures 0 <= c.data ==> old(c.data) <= SP(c, y) == c.Plus(y)
  {
  }

  method CallLemmas<Y>(c: Cell, b: bool, y: Y)
    modifies c
  {
    c.data := c.data + 1;  // +1
    label OneMore:
    if -1 <= old(c.data) {
      TwoLemma(c, y);
    }

    c.data := c.data + 4;  // +5
    label FiveMore:
    TwoLemma@OneMore(c, y);  // fine

    if b {
      c.data := c.data - 10;  // -5
      TwoLemma@FiveMore(c, y);  // error: precondition violation
    } else {
      c.data := c.data + 2;  // +7
    }
    c.LL(y);
    c.LL(0);
    assert !b;  // follows from the control flow above and LL's (bogus) postcondition
  }

  twostate function {:opaque} Opaque(c: Cell): int { old(c.data) + 12 }
  method UseOpaque(c: Cell)
    requires c.data == 100
    modifies c
  {
    c.data := c.data + 5;
    label L:
    c.data := c.data + 2;

    var y112 := Opaque(c);
    var y117 := Opaque@L(c);

    if * {
      assert y112 == 112;  // error: don't konw Opaque's definition
    } else if * {
      assert y117 == 117;  // error: don't konw Opaque's definition
    } else {
      reveal Opaque();  // this gets Opaque for all possible parameters, including for all labels
      assert y112 == 112;
      assert y117 == 117;
    }
    assert c.data == 107;
  }
  twostate function FuncUseOpaque(c: Cell, b: bool): int {
    reveal Opaque();
    10
  }

  method Allocatedness_Function() {
    label A:
    var c := new Cell(5);
    label B:
    label C:
    c.data := c.data + 400;
    label D:

    if {
      case true =>
        var a := c.Plus(0);  // error: c not allocated in old state
      case true =>
        var a := c.Plus@A(0);  // error: c not allocated in state A
      case true =>
        var a := c.Plus@B(0) + c.Plus@C(0) + c.Plus@D(0);
        assert a == 5 + 5 + 405 + 1215;
      case true =>
        var u := Cell.Sum(c, 0);  // error: c not allocated in old state
      case true =>
        var a := Cell.Sum@A(c, 0);  // error: c not allocated in state A
      case true =>
        var a := Cell.Sum@B(c, 0) + Cell.Sum@C(c, 0) + Cell.Sum@D(c, 0);
        assert a == 5 + 5 + 405 + 1215;
      case true =>
        var a := c.Plus<int>;  // error: c not allocated in old state
    }
  }

  method Allocatedness_Lemma() {
    label A:
    var c := new Cell(5);
    label B:
    label C:
    c.data := c.data + 400;
    label D:

    if {
      case true =>
        c.LL(0);  // error: c not allocated in old state
      case true =>
        c.LL@A(0);  // error: c not allocated in state A
      case true =>
        c.LL@B(0);
        c.LL@C(0);
        c.LL@D(0);
      case true =>
        Cell.IdentityLemma(c, 0);  // error: c not allocated in old state
      case true =>
        Cell.IdentityLemma@A(c, 0);  // error: c not allocated in state A
      case true =>
        Cell.IdentityLemma@B(c, 0);
        Cell.IdentityLemma@C(c, 0);
        Cell.IdentityLemma@D(c, 0);
    }
  }

  twostate function FuncMoreParams(c: Cell, new d: Cell): int { 7 }
  twostate lemma LemmaMoreParams(c: Cell, new d: Cell) returns (e: Cell) {
    if * {
      e := c;
    } else {
      e := d;
    }
  }
  method TestFuncMoreParams(c0: Cell) {
    var c1 := new Cell(1);
    label L:
    var c2 := new Cell(2);
    ghost var x;

    if {
      case true =>
        x := FuncMoreParams(c0, c0);
        x := FuncMoreParams(c1, c0);  // error: c1 not allocated in old state
      case true =>
        x := FuncMoreParams@L(c0, c0);
        x := FuncMoreParams@L(c1, c0);
        x := FuncMoreParams@L(c2, c0);  // error: c2 not allocated in state L
      case true =>
        x := FuncMoreParams(c0, c1);
        x := FuncMoreParams(c0, c2);
    }
  }
  method TestLemmaMoreParams(c0: Cell) {
    var c1 := new Cell(1);
    label L:
    var c2 := new Cell(2);
    ghost var x;

    if {
      case true =>
        x := LemmaMoreParams(c0, c0);
        x := LemmaMoreParams(c1, c0);  // error: c1 not allocated in old state
      case true =>
        x := LemmaMoreParams@L(c0, c0);
        x := LemmaMoreParams@L(c1, c0);
        x := LemmaMoreParams@L(c2, c0);  // error: c2 not allocated in state L
      case true =>
        x := LemmaMoreParams(c0, c1);
        x := LemmaMoreParams(c0, c2);
    }
  }

  datatype DT<X> = Green | Blue(value: X) {
    static const sc := 18
    twostate function F<Y>(x: X, y: Y, c: Cell): int
      reads c
    {
      c.data - old(c.data)
    }
    twostate lemma L<Y>(x: X, y: Y, c: Cell) returns (n: nat)
      requires old(c.data) <= c.data
    {
      n := F(x, y, c);
    }
    static twostate function G<Y>(x: X, y: Y, c: Cell): int
      reads c
    {
      Green.F(x, y, c)
    }
    static twostate lemma M<Y>(x: X, y: Y, c: Cell) returns (n: nat)
      requires old(c.data) <= c.data
    {
      n := Green.L(x, y, c);
    }
  }

  newtype NT = x | 0 <= x < 86 {
    const value := 18
    static const sc := 18
    twostate function F<Y>(y: Y, c: Cell): int
      reads c
    {
      c.data - old(c.data)
    }
    twostate lemma L<Y>(y: Y, c: Cell) returns (n: nat)
      requires old(c.data) <= c.data
    {
      n := F(y, c);
    }
    static twostate function G<Y>(y: Y, c: Cell): int
      reads c
    {
      (82 as NT).F(y, c)
    }
    static twostate lemma M<Y>(y: Y, c: Cell) returns (n: nat)
      requires old(c.data) <= c.data
    {
      n := (82 as NT).L(y, c);
    }
  }

  type OT<X> {
    const value := 18
    static const sc := 18
    twostate function F<Y>(x: X, y: Y, c: Cell): int
      reads c
    {
      c.data - old(c.data)
    }
    twostate lemma L<Y>(x: X, y: Y, c: Cell) returns (n: nat)
      requires old(c.data) <= c.data
    {
      n := F(x, y, c);
    }
    static twostate function G<Y>(ot: OT<X>, x: X, y: Y, c: Cell): int
      reads c
    {
      ot.F(x, y, c)
    }
    static twostate lemma M<Y>(ot: OT<X>, x: X, y: Y, c: Cell) returns (n: nat)
      requires old(c.data) <= c.data
    {
      n := ot.L(x, y, c);
    }
  }

  method TestOthers0(dt: DT<real>, nt: NT, ot: OT<bv19>, r: real, t: bv19, u: ()) {
    var c := new Cell(333);
    label Label:
    ghost var n, x, y;

    if * {
      x := dt.F@Label(r, u, c);
      x := dt.F(r, u, c);  // error: c is not in old state
    } else if * {
      n := dt.L@Label(r, u, c);
      n := dt.L(r, u, c);  // error: c is not in old state
    } else if * {
      y := DT.G@Label(r, u, c);
      y := DT.G(r, u, c);  // error: c is not in old state
    } else if * {
      n := DT.M@Label(r, u, c);
      n := DT.M(r, u, c);  // error: c is not in old state
    }
  }

  method TestOthers1(nt: NT, ot: OT<bv19>, r: Cell, t: bv19, u: (), c: Cell) {
    var dtx := new Cell(333);
    var dt := Blue(dtx);
    label Label:
    ghost var n, x;

    if * {
      x := dt.F@Label(r, u, c);
      x := dt.F(r, u, c);  // error: receiver is not in old state
    } else if * {
      n := dt.L@Label(r, u, c);
      n := dt.L(r, u, c);  // error: receiver is not in old state
    }
  }

  method TestOthers2(dt: DT<real>, nt: NT, ot: OT<bv19>, r: real, t: bv19, u: ()) {
    var c := new Cell(333);
    label Label:
    ghost var n, x, y;

    if * {
      x := nt.F@Label(u, c);
      x := nt.F(u, c);  // error: c is not in old state
    } else if * {
      n := nt.L@Label(u, c);
      n := nt.L(u, c);  // error: c is not in old state
    } else if * {
      y := NT.G@Label(u, c);
      y := NT.G(u, c);  // error: c is not in old state
    } else if * {
      n := NT.M@Label(u, c);
      n := NT.M(u, c);  // error: c is not in old state
    }
  }

  method TestOthers3(dt: DT<real>, nt: NT, ot: OT<bv19>, r: real, t: bv19, u: ()) {
    var c := new Cell(333);
    label Label:
    ghost var n, x, y;

    if * {
      x := ot.F@Label(t, u, c);
      x := ot.F(t, u, c);  // error: c is not in old state
    } else if * {
      n := ot.L@Label(t, u, c);
      n := ot.L(t, u, c);  // error: c is not in old state
    } else if * {
      y := OT.G@Label(ot, t, u, c);
      y := OT.G(ot, t, u, c);  // error: c is not in old state
    } else if * {
      n := OT.M@Label(ot, t, u, c);
      n := OT.M(ot, t, u, c);  // error: c is not in old state
    }
  }

  method TestOthers4(d0: DT<Cell>, nt: NT, ot: OT<Cell>, r: Cell, u: ()) {
    var c := new Cell(333);
    var d1 := Blue(c);
    label Label:

    if * {
      ghost var f0 := d0.F<int>;
      ghost var f1 := nt.F<int>;
      ghost var f2 := ot.F<int>;
      ghost var f3 := d1.F<int>;  // error: receiver is not in old state
    } else if * {
      ghost var g0 := DT<Cell>.G<int>;
      ghost var g1 := NT.G<int>;
      ghost var g2 := OT<Cell>.G<int>;
    } else if * {
      ghost var h0 := d0.G<int>;
      ghost var h1 := nt.G<int>;
      ghost var h2 := ot.G<int>;
      ghost var h3 := d1.G<int>;  // this is also fine
    }
  }

  method FieldAccess(d0: DT<Cell>, nt: NT, ot: OT<Cell>, r: Cell, u: ())
    requires d0.Blue?
  {
    var c := new Cell(333);
    var d1 := Blue(c);
    label Label:

    if * {
      ghost var f0 := old(d0.value);
      ghost var f1 := old(nt.value);
      ghost var f2 := old(ot.value);
      ghost var f3 := old(d1.value);  // error: receiver is not in old state
    } else if * {
      ghost var g0 := old(DT<Cell>.sc);
      ghost var g1 := old(NT.sc);
      ghost var g2 := old(OT<Cell>.sc);
    } else if * {
      ghost var h0 := old(d0.sc);
      ghost var h1 := old(nt.sc);
      ghost var h2 := old(ot.sc);
      ghost var h3 := old(d1.sc);  // this is also fine
    } else if * {
      ghost var f0 := old@Label(d0.value);
      ghost var f1 := old@Label(nt.value);
      ghost var f2 := old@Label(ot.value);
      ghost var f3 := old@Label(d1.value);  // fine
    } else if * {
      ghost var g0 := old@Label(DT<Cell>.sc);
      ghost var g1 := old@Label(NT.sc);
      ghost var g2 := old@Label(OT<Cell>.sc);
    } else if * {
      ghost var h0 := old@Label(d0.sc);
      ghost var h1 := old@Label(nt.sc);
      ghost var h2 := old@Label(ot.sc);
      ghost var h3 := old@Label(d1.sc);
    }
  }
}

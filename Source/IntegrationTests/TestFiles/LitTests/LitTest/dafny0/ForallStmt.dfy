// UNSUPPORTED: windows
// RUN: %exits-with 4 %verify --allow-axioms --manual-triggers "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
class C {
  var data: int
  var n: nat
  var st: set<object>

  lemma CLemma(k: int)
    requires k != -23
    ensures data < k  // magic, isn't it (or bogus, some would say)
}

// This method more or less just tests the syntax, resolution, and basic verification
method ParallelStatement_Resolve(
    a: array<int>,
    spine: set<C>,
    Repr: set<object>,
    S: set<int>,
    clx: C?, cly: C?, clk: int
  )
  modifies a, spine
{
  forall i | 0 <= i < a.Length && i % 2 == 0 {
    a[i] := a[(i + 1) % a.Length] + 3;
  }

  forall o | o in spine {
    o.st := o.st + Repr;
  }

  forall x, y | x in S && 0 <= y+x < 100 {
    Lemma(clx, x, y);  // error: precondition does not hold (clx may be null)
  }

  forall x, y | x in S && 0 <= y+x < 100 {
    cly.CLemma(x + y);  // error: receiver might be null
  }

  forall p | 0 <= p
    ensures F(p) <= Sum(p) + p - 1  // error (no connection is known between F and Sum)
  {
    assert 0 <= G(p);
    ghost var t;
    if p % 2 == 0 {
      assert G(p) == F(p+2);  // error (there's nothing that gives any relation between F and G)
      t := p+p;
    } else {
      assume H(p, 20) < 100;  // don't know how to justify this
      t := p;
    }
    PowerLemma(p, t);
    t := t + 1;
    PowerLemma(p, t);
  }
}

lemma Lemma(c: C?, x: int, y: int)
  requires c != null
  ensures c.data <= x+y
lemma PowerLemma(x: int, y: int)
  ensures Pred(x, y)

ghost function F(x: int): int
ghost function G(x: int): nat
ghost function H(x: int, y: int): int
ghost function Sum(x: int): int
ghost function Pred(x: int, y: int): bool

// ---------------------------------------------------------------------

method M0(S: set<C>)
  modifies S
  ensures forall o :: o in S ==> o.data == 85
  ensures forall o :: o !in S && o != null && !fresh(o) ==> o.data == old(o.data)
{
  forall s | s in S {
    s.data := 85;
  }
}

method M1(S: set<C>, x: C)
  requires x in S
{
  forall s | s in S
    ensures s.data < 100
  {
    assume s.data == 85;
  }
  if * {
    assert x.data == 85;  // error (cannot be inferred from forall ensures clause)
  } else {
    assert x.data < 120;
  }

  forall s | s in S
    ensures s.data < 70  // error
  {
    assume s.data == 85;
  }
}

method M2() returns (a: array<int>)
  ensures forall i,j :: 0 <= i < a.Length/2 <= j < a.Length ==> a[i] < a[j]
{
  a := new int[250];
  forall i: nat | i < 125 {
    a[i] := 423;
  }
  forall i | 125 <= i < 250 {
    a[i] := 300 + i;
  }
}

method M4(S: set<C>, k: int)
  modifies S
{
  forall s | s in S {
    s.n := k;  // error: k might be negative
  }
}

method M5()
{
  if {
  case true =>
    forall x | 0 <= x < 100 {
      PowerLemma(x, x);
    }
    assert Pred(34, 34);

  case true =>
    forall x,y | 0 <= x < 100 && y == x+1 {
      PowerLemma(x, y);
    }
    assert Pred(34, 35);

  case true =>
    forall x,y | 0 <= x < y < 100 {
      PowerLemma(x, y);
    }
    assert Pred(34, 35);

  case true =>
    forall x | x in set k | 0 <= k < 100 {
      PowerLemma(x, x);
    }
    assert Pred(34, 34);
  }
}

method Main()
{
  var a := new int[180];
  forall i | 0 <= i < 180 {
    a[i] := 2*i + 100;
  }
  var sq := [0, 0, 0, 2, 2, 2, 5, 5, 5];
  forall i | 0 <= i < |sq| {
    a[20+i] := sq[i];
  }
  forall t | t in sq {
    a[t] := 1000;
  }
  forall t,u | t in sq && t < 4 && 10 <= u < 10+t {
    a[u] := 6000 + t;
  }
  var k := 0;
  while k < 180 {
    if k != 0 { print ", "; }
    print a[k];
    k := k + 1;
  }
  print "\n";
}

method DuplicateUpdate() {
  var a := new int[180];
  var sq := [0, 0, 0, 2, 2, 2, 5, 5, 5];
  if * {
    forall t,u | t in sq && 10 <= u < 10+t {
      a[u] := 6000 + t;  // error: a[10] (and a[11]) are assigned more than once
    }
  } else {
    forall t,u | t in sq && t < 4 && 10 <= u < 10+t {
      a[u] := 6000 + t;  // with the 't < 4' conjunct in the line above, this is fine
    }
  }
}

lemma DontDoMuch(x: int)
{
}

method OmittedRange() {
  forall x: int { }  // a type is still needed for the bound variable
  forall x {
    DontDoMuch(x);
  }
}

// ----------------------- two-state postconditions ---------------------------------

class TwoState_C { ghost var data: int }

// It is not possible to achieve this postcondition in a lemma, because lemma
// contexts are not allowed to allocate state.  Callers of this lemma will know
// that the postcondition is tantamount to 'false'.
lemma TwoState0(y: int)
  ensures exists o: TwoState_C {:nowarn} :: allocated(o) && fresh(o)

method TwoState_Main0() {
  forall x { TwoState0(x); }
  assert false;  // no prob, because the postcondition of TwoState0 implies false
}

method X_Legit(c: TwoState_C)
  modifies c
{
  c.data := c.data + 1;
  forall x | c.data <= x
    ensures old(c.data) < x  // note that the 'old' refers to the method's initial state
  {
  }
}

// At first glance, this looks like a version of TwoState_Main0 above, but with an
// ensures clause.
// However, there's an important difference in the translation, which is that the
// occurrence of 'fresh' here refers to the initial state of the TwoStateMain2
// method, not the beginning of the 'forall' statement.
method TwoState_Main2()
{
  forall x: int
    ensures exists o: TwoState_C {:nowarn} :: allocated(o) && fresh(o)
  {
    TwoState0(x);
  }
  assert false;  // fine, for the postcondition of the forall statement implies false
}

// At first glance, this looks like an inlined version of TwoState_Main0 above.
// However, there's an important difference in the translation, which is that the
// occurrence of 'fresh' here refers to the initial state of the TwoState_Main3
// method, not the beginning of the 'forall' statement.
// Still, care needs to be taken in the translation to make sure that the forall
// statement's effect on the heap is not optimized away.
method TwoState_Main3()
{
  forall x: int
    ensures exists o: TwoState_C {:nowarn} :: allocated(o) && fresh(o)
  {
    assume false;  // (there's no other way to achieve this forall-statement postcondition)
  }
  assert false;  // it is known that the forall's postcondition is contradictory, so this assert is fine
}

// ---------------------------------------------------------------------
// The following is an example that once didn't verify (because the forall statement that
// induction inserts had caused the $Heap to be advanced, despite the fact that Th is a
// ghost method).

datatype Nat = Zero | Succ(tail: Nat)

ghost predicate ThProperty(step: nat, t: Nat, r: nat)
{
  match t
  case Zero => true
  case Succ(o) => step>0 && exists ro:nat, ss | ss == step-1 :: ThProperty(ss, o, ro) //WISH: ss should be autogrnerated. Note that step is not a bound variable.
}

lemma Th(step: nat, t: Nat, r: nat)
  requires t.Succ? && ThProperty(step, t, r)
  // the next line follows from the precondition and the definition of ThProperty
  ensures exists ro:nat, ss | ss == step-1 :: ThProperty(ss, t.tail, ro) //WISH same as above
{
}

// ------------------------------------------------------------------------
// The following example once included a unsoundness bug in the translation

method BogosityClient()
  ensures false
{
  var c := new C;
  c.data := 3;
  Bogus(c);
}

ghost predicate False(x: int) { false }

method Bogus(c: C)
  requires c.data == 3
  modifies c
  ensures false
{
  c.data := 4;
  forall x | old(c.data) == 4
    ensures False(x)
  {
    // easily provable, because the range of x is empty
  }
  assert False(10);  // error: does not follow from the "forall" statement
}

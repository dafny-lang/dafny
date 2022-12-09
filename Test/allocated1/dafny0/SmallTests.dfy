// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %dafny /verifyAllModules /allocated:1 /noVerify /compile:0 "%t.dprint.dfy" >> "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  var next: Node?

  predicate IsList(r: set<Node>)
    reads r
  {
    this in r &&
    (next != null  ==>  next.IsList(r - {this}))
  }

  method Test(n: Node, nodes: set<Node>)
  {
    assume nodes == nodes - {n};
    // the next line needs the Set extensionality axiom, the antecedent of
    // which is supplied by the previous line
    assert IsList(nodes) == IsList(nodes - {n});
  }

  method Create()
    modifies this
  {
    next := null;
    var tmp: Node;
    tmp := new Node;
    assert tmp != this;  // was once a bug in the Dafny checker
  }

  method SequenceUpdateOutOfBounds(s: seq<set<int>>, j: int) returns (t: seq<set<int>>)
  {
    t := s[j := {}];  // error: j is possibly out of bounds
  }

  method Sequence(s: seq<bool>, j: int, b: bool, c: bool) returns (t: seq<bool>)
    requires 10 <= |s|
    requires 8 <= j < |s|
    ensures |t| == |s|
    ensures t[8] == s[8] || t[9] == s[9]
    ensures t[j] == b
  {
    if (c) {
      t := s[j := b];
    } else {
      t := s[..j] + [b] + s[j+1..];
    }
  }

  method Max0(x: int, y: int) returns (r: int)
    ensures r == (if x < y then y else x)
  {
    if (x < y) { r := y; } else { r := x; }
  }

  method Max1(x: int, y: int) returns (r: int)
    ensures r == x || r == y
    ensures x <= r && y <= r
  {
    r := if x < y then y else x;
  }

  function PoorlyDefined(x: int): int
    requires if next == null then 5/x < 20 else true;  // error: ill-defined then branch
    requires if next == null then true else 0 <= 5/x;  // error: ill-defined then branch
    requires if next.next == null then true else true;  // error: ill-defined guard
    requires 10/x != 8;  // this is well-defined, because we get here only if x is non-0
    reads this, next;
  {
    12
  }
}

// ------------------ modifies clause tests ------------------------

class Modifies {
  var x: int
  var next: Modifies?

  method A(p: Modifies?)
    modifies this, p
  {
    x := x + 1;
    while p != null && p.x < 75
      decreases 75 - p.x  // error: not defined (null deref) at top of each iteration (there's good reason
    {                      // to insist on this; for example, the decrement check could not be performed
      p.x := p.x + 1;      // at the end of the loop body if p were set to null in the loop body)
    }
  }

  method Aprime(p: Modifies?)
    modifies this, p
  {
    x := x + 1;
    while p != null && p.x < 75
      decreases if p != null then 75 - p.x else 0  // given explicitly (but see Adoubleprime below)
    {
      p.x := p.x + 1;
    }
  }

  method Adoubleprime(p: Modifies?)
    modifies this, p
  {
    x := x + 1;
    while p != null && p.x < 75  // here, the decreases clause is heuristically inferred (to be the
    {                              // same as the one in Aprime above)
      p.x := p.x + 1;
    }
  }

  method B(p: Modifies)
    modifies this
  {
    A(this);
    if p == this {
      p.A(p);
    }
    A(p);  // error: may violate modifies clause
  }

  method C(b: bool)
    modifies this
    ensures !b ==> x == old(x) && next == old(next)
  {
  }

  method D(p: Modifies, y: int)
  {
    if (y == 3) {
      p.C(true);  // error: may violate modifies clause
    } else {
      p.C(false);  // error: may violation modifies clause (the check is done without regard
                   // for the postcondition, which also makes sense, since there may, in
                   // principle, be other fields of the object that are not constrained by the
                   // postcondition)
    }
  }

  method E()
    modifies this
  {
    A(null);  // allowed
  }

  method F(s: set<Modifies>)
    modifies s
  {
    forall m | m in s && 2 <= m.x {
      m.x := m.x + 1;
    }
    if this in s {
      x := 2 * x;
    }
  }

  method G(s: set<Modifies>)
    modifies this
  {
    var m := 3;  // this is a different m

    forall m | m in s && m == this {
      m.x := m.x + 1;
    }
    if (s <= {this}) {
      forall (m | m in s) {
        m.x := m.x + 1;
      }
      F(s);
    }
    forall (m | m in s) ensures true; { assert m.x < m.x + 10; }
    forall (m | m in s) {
      m.x := m.x + 1;  // error: may violate modifies clause
    }
  }

  method SetConstruction() {
    var s := {1};
    assert s != {};
    if (*) {
      assert s != {0,1};
    } else {
      assert s != {1,0};
    }
  }
}

// ------------------ allocated --------------------------------------------------

class AllocatedTests {
  method M()
  {
    var n := new Node;
    if
    case true =>  assert old(allocated(n));  // error: n was not allocated in the initial state
    case true =>  assert !fresh(n);  // error: n was not allocated in the initial state
    case true =>  assert fresh(n) && !old(allocated(n)) && allocated(n);  // correct
    case true =>  assert fresh(null);  // error: null is never fresh
    case true =>  assert !fresh(null);
    case true =>  assert allocated(null);  // null is a literal, so it is always allocated
  }
  method Set0(k: Node?)
  {
    var n := new Node;
    var U := {k,n};
    if
    case true =>  assert allocated(U);  // everytning is always allocated in the current state
    case true =>  assert old(allocated(U));  // error: n was not allocated initially
    case true =>  assert !old(allocated(U));
    case true =>  assert fresh(U);  // error: k may be null (or was allocated initially)
    case k == null =>  assert fresh(U);  // error: k is null, so fresh returns false
    case k == null =>  assert !fresh(U);
    case k != null =>  assert fresh(U);  // error: k was allocated initially
    case k != null =>  assert !fresh(U);
  }
  method Set1(k: Node?)
  {
    M();  // a method call, which introduces another allocation state
    var n: Node?;  // null or an allocated object of type Node
    var U := {k,n};
    if
    case true =>  assert old(allocated(U));  // error: n may be an object allocated inside M()
    case n == null =>  assert old(allocated(U));  // yes
    case n == null =>  assert fresh(U);  // error: fresh is always false for null
    case !old(allocated(n)) =>  assert n != null;
    case !old(allocated(n)) =>  assert fresh(n);  // yes, if n was not available initially, then it is non-null and fresh
    case fresh(n) =>  assert n != null;
  }
  method Seq0(k: Node?)
  {
    var n := new Node;
    var U := [k,n];
    if
    case true =>  assert allocated(U);  // everytning is always allocated in the current state
    case true =>  assert old(allocated(U));  // error: n was not allocated initially
    case true =>  assert !old(allocated(U[1]));  // this is a lemma that helps prove the next line
                  assert !old(allocated(U));
    case true =>  assert fresh(U);  // error: k may be null (or was allocated initially)
    case k == null =>  assert fresh(U);  // error: k is null, so fresh returns false
    case k == null =>  assert !fresh(U[0]);  // this is a lemma that helps prove the next line
                        assert !fresh(U);
    case k != null =>  assert fresh(U);  // error: k was allocated initially
    case k != null =>  assert !fresh(U[0]);  // this is a lemma that helps prove the next line
                        assert !fresh(U);
  }
  method Seq1(k: Node?)
  {
    M();  // a method call, which introduces another allocation state
    var n: Node?;  // null or an allocated object of type Node
    var U := [k,n];
    if
    case true =>  assert old(allocated(U));  // error: n may be an object allocated inside M()
    case n == null =>  assert old(allocated(U));  // yes
    case n == null =>  assert fresh(U);  // error: fresh is always false for null
    case !old(allocated(n)) =>  assert n != null;
    case !old(allocated(n)) =>  assert fresh(n);  // yes, if n was not available initially, then it is non-null and fresh
    case fresh(n) =>  assert n != null;
  }
}

datatype Lindgren =
  Pippi(Node) |
  Longstocking(seq<object>, Lindgren) |
  HerrNilsson

// --------------------------------------------------

class InitCalls {
  var z: int
  var p: InitCalls?

  method Init(y: int)
    modifies this
    ensures z == y
  {
    z := y;
  }

  method InitFromReference(q: InitCalls)
    requires 15 <= q.z
    modifies this;
    ensures p == q
  {
    p := q;
  }

  method TestDriver()
  {
    var c: InitCalls;
    c := new InitCalls.Init(15);
    var d := new InitCalls.Init(17);
    var e: InitCalls := new InitCalls.Init(18);
    var f: object := new InitCalls.Init(19);
    assert c.z + d.z + e.z == 50;

    assert var g: InitCalls := f; f == g;
    assert var g: InitCalls := f; g.z == 19;

    // test that the call is done before the assignment to the LHS
    var r := c;
    r := new InitCalls.InitFromReference(r);  // fine, since r.z==15
    r := new InitCalls.InitFromReference(r);  // error, since r.z is unknown
  }
}

// --------------- some tests with quantifiers and ranges ----------------------

method QuantifierRange0<T>(a: seq<T>, x: T, y: T, N: int)
  requires 0 <= N <= |a|
  requires forall k | 0 <= k < N :: a[k] != x
  requires exists k | 0 <= k < N :: a[k] == y
  ensures forall k :: 0 <= k < N ==> a[k] != x;  // same as the precondition, but using ==> instead of |
  ensures exists k :: 0 <= k < N && a[k] == y;  // same as the precondition, but using && instead of |
{
  assert x != y;
}

method QuantifierRange1<T>(a: seq<T>, x: T, y: T, N: int)
  requires 0 <= N <= |a|
  requires forall k :: 0 <= k < N ==> a[k] != x
  requires exists k :: 0 <= k < N && a[k] == y
  ensures forall k | 0 <= k < N :: a[k] != x;  // same as the precondition, but using | instead of ==>
  ensures exists k | 0 <= k < N :: a[k] == y;  // same as the precondition, but using | instead of &&
{
  assert x != y;
}

method QuantifierRange2<T(==)>(a: seq<T>, x: T, y: T, N: int)
  requires 0 <= N <= |a|
  requires exists k | 0 <= k < N :: a[k] == y
  ensures forall k | 0 <= k < N :: a[k] == y;  // error
{
  assert N != 0;
  if (N == 1) {
    assert forall k {:nowarn} | a[if 0 <= k < N then k else 0] != y :: k < 0 || N <= k;  // in this case, the precondition holds trivially
  }
  if (forall k | 0 <= k < N :: a[k] == x) {
    assert x == y;
  }
}

// ----------------------- tests that involve sequences of boxes --------

ghost method M(zeros: seq<bool>, Z: bool)
  requires 1 <= |zeros| && Z == false
  requires forall k :: 0 <= k < |zeros| ==> zeros[k] == Z
{
  var x := [Z];
  assert zeros[0..1] == [Z];
}

class SomeType
{
  var x: int;
  method DoIt(stack: seq<SomeType>)
    modifies stack;
  {
    forall n | n in stack {
      n.x := 10;
    }
  }
}

// ----------------------- tests of some theory axioms --------

method TestSequences0()
{
  var s := [0, 2, 4];
  if (*) {
    assert 4 in s;
    assert 0 in s;
    assert 1 !in s;
  } else {
    assert 2 in s;
    assert 0 in s;
    assert exists n :: n in s && -3 <= n < 2;
  }
  assert 7 in s;  // error
}

// ----------------------- test attributes on methods and constructors --------

method test0()
{
  assert false;  // error
}

method {:verify false} test1()
{
  assert false;
}

function test2() : bool
{
  !test2()  // error
}

function {:verify false} test3() : bool
{
  !test3()
}

class Test {

  method test0()
  {
    assert false;  // error
  }

  method {:verify false} test1()
  {
    assert false;
  }

  constructor init0()
  {
    assert false;  // error
  }

  constructor {:verify false} init1()
  {
    assert false;
  }

  function test2() : bool
  {
    !test2()  // error
  }

  function {:verify false} test3() : bool
  {
    !test3()
  }

}

// ------ an if-then-else regression test

function F(b: bool): int
  // The if-then-else in the following line was once translated incorrectly,
  // incorrectly causing the postcondition to verify
  ensures if b then F(b) == 5 else F(b) == 6
{
  5
}

// ----------------------- test attributes on method specification constructs (assert, ensures, modifies, decreases, invariant) --------

class AttributeTests {
  var f: int;

  method m0()
  {

  }

  method m1() returns (r: bool)
  {
    r := false;
  }

  function method m2() : bool
  {
    true
  }

  constructor C()
  {

  }

  method testAttributes0() returns (r: AttributeTests)
    ensures {:boolAttr true} true
    ensures {:boolAttr false} true
    ensures {:intAttr 0} true
    ensures {:intAttr 1} true
    modifies {:boolAttr true} this`f;
    modifies {:boolAttr false} this`f;
    modifies {:intAttr 0} this`f;
    modifies {:intAttr 1} this`f;
    modifies {:boolAttr true} this;
    modifies {:boolAttr false} this;
    modifies {:intAttr 0} this;
    modifies {:intAttr 1} this;
    decreases {:boolAttr true} f;
    decreases {:boolAttr false} f;
    decreases {:intAttr 0} f;
    decreases {:intAttr 1} f;
  {
    assert {:boolAttr true} true;
    assert {:boolAttr false} true;
    assert {:intAttr 0} true;
    assert {:intAttr 1} true;

    while (false)
      invariant {:boolAttr true} true;
      invariant {:boolAttr false} true;
      invariant {:intAttr 0} true;
      invariant {:intAttr 1} true;
      modifies {:boolAttr true} this`f;
      modifies {:boolAttr false} this`f;
      modifies {:intAttr 0} this`f;
      modifies {:intAttr 1} this`f;
      decreases {:boolAttr true} f;
      decreases {:boolAttr false} f;
      decreases {:intAttr 0} f;
      decreases {:intAttr 1} f;
    {

    }

    m0() {:boolAttr true};
    m0() {:boolAttr false};
    m0() {:intAttr 0};
    m0() {:intAttr 1};

    this.m0() {:boolAttr true};
    this.m0() {:boolAttr false};
    this.m0() {:intAttr 0};
    this.m0() {:intAttr 1};

    var b1 := m1() {:boolAttr true};
    b1 := m1() {:boolAttr false};
    b1 := m1() {:intAttr 0};
    b1 := m1() {:intAttr 1};

    var b2, b2' := m2() {:boolAttr true}, m2() {:boolAttr true};
    b2, b2' := m2() {:boolAttr false}, m2() {:boolAttr false};
    b2, b2' := m2() {:intAttr 0}, m2() {:boolAttr false};
    b2, b2' := m2() {:intAttr 1}, m2() {:boolAttr false};

    var c := new AttributeTests.C() {:boolAttr true};
    c := new AttributeTests.C() {:boolAttr false};
    c := new AttributeTests.C() {:intAttr 0};
    c := new AttributeTests.C() {:intAttr 1};

    if (*) {
      return new AttributeTests.C() {:boolAttr true};
    } else {
      return new AttributeTests.C() {:intAttr 0};
    }

    // forall statements resolve their attributes once the bound variables have been
    // added to the scope
    var y: bool, x: real;
    var aa := new real[120];
    forall y: int, x, z {:trgr x == y} {:tri z == z} | x < y  // the range will infer the type of x
      ensures z && 0 <= x < aa.Length ==> aa[x] == 0.0;  // ensures clause will infer type of z
    {
    }
  }
}

// ----------------------- test attributes on variable declarations --------

method TestAttributesVarDecls()
{
  var {:foo foo} foo := null;
  var {:bar bar} bar := 0;
  var {:foo foobar} {:bar foobar} foobar : set<int> := {};
  var {:baz baz && foobaz} baz, {:foobaz foobaz != baz} foobaz := true, false;
}

// ----------------------- Pretty printing of !(!expr) --------

method TestNotNot()
{
  assert !(!true);  // Shouldn't pretty print as "!!true".

  assert !(true == false);

  assert !(if true then false else false);

  assert !if true then false else false;

  assert !if !(!true) then false else false;

  assert true == !(!true);
}

// ----------------------- Assign-such-that statements -------

method AssignSuchThat0(a: int, b: int) returns (x: int, y: int)
  ensures x == a && y == b
{
  if (*) {
    x, y :| a <= x < a + 1 && b + a <= y + a && y <= b;
  } else {
    var xx, yy :| a <= xx < a + 1 && b + a <= yy + a && yy <= b;
    x, y := xx, yy;
  }
}

method AssignSuchThat1(a: int, b: int) returns (x: int, y: int)
{
  ghost var k :| assume 0 <= k < a - b;  // this acts like an 'assume 0 < a - b;'
  assert b < a;
  k :| k == old(2*k);  // note, the 'old' has no effect on local variables like k
  assert k == 0;
  var S := {2, 4, 7};
  var T :| T <= S;
  assert 3 !in T;
  assert T == {};  // error: T may be larger
}

method AssignSuchThat2(i: int, j: int, ghost S: set<Node>)
  modifies S;
{
  var n := new Node;
  var a := new int[25];
  var t;
  if (0 <= i < j < 25) {
    a[i], t, a[j], n.next, n :| assume allocated(n);
  }
  if (n.next != null) {
    assume n in S && n.next in S;
    n.next.next, n.next :| assume n.next != null && n.next.next == n.next;  // error: n.next may equal n (thus aliasing n.next.next and n.next)
  } else if (0 <= i < 25 && 0 <= j < 25) {
    t, a[i], a[j] :| assume t < a[i] < a[j];  // error: i may equal j (thus aliasing a[i] and a[j])
  }
}

method AssignSuchThat3()
{
  var n: Node? := new Node;
  n, n.next :| assume n.next == n;  // error: RHS is not well defined (RHS is evaluated after the havocking of the LHS)
}

method AssignSuchThat4()
{
  var n: Node? := new Node;
  n, n.next :| assume n != null && allocated(n) && n.next == n;  // that's the ticket
}

method AssignSuchThat5()
{
  var k := new Node;
  ghost var n: Node :| fresh(n);  // fine
  assert false;  // error
}

method AssignSuchThat6()
{
  var n: Node;
  n :| assume fresh(n);  // there is no non-null fresh object, so this amounts to 'assume false;'
  assert false;  // no problemo
}

method AssignSuchThat7<T>(A: set<T>, x: T) {
  var B :| B <= A;
  assert x in B ==> x in A;
}

method AssignSuchThat8(n: int) returns (x: int, y: Lindgren) {
  x :| x in {1};
  x :| x in {3, 7, 11};
  x :| x in {n + 12};
  y :| y in {HerrNilsson};
  y :| y == y;
  x :| x in multiset{3, 3, 2, 3};
  x :| x in map[5 := 10, 6 := 12];
  x :| x in [n, n, 2];
  x :| x in [];  // error
}

codatatype QuiteFinite = QQA | QQB | QQC

method AssignSuchThat9() returns (q: QuiteFinite)
{
  q :| q != QQA && q != QQC;
}

// ----------- let-such-that expressions ------------------------

function method LetSuchThat_P(x: int): bool

method LetSuchThat0(ghost g: int)
  requires LetSuchThat_P(g)
{
  var t :| LetSuchThat_P(t);  // assign-such-that statement
  ghost var u := var q :| LetSuchThat_P(q); q + 1;  // let-such-that expression
  if (forall a,b | LetSuchThat_P(a) && LetSuchThat_P(b) :: a == b) {
    assert t < u;
  }
  assert LetSuchThat_P(u-1);  // yes
  assert LetSuchThat_P(u);  // error: no reason to expect this to hold
}

method LetSuchThat1<T>(A: set<T>)
{
  ghost var C := var B :| B <= A; B - A;
  assert C == {};
}

method LetSuchThat2(n: nat)
{
  ghost var x := (var k :| k < n; k) + 3;  // fine, such a k always exists
  assert x < n+3;
  if (*) {
    x := var k :| 0 <= k < n; k;  // error: there may not be such a k
  } else {
    x := var k: nat :| k < n; k;  // error: there may not be such a k
  }
}

ghost method LetSuchThat3(n: int) returns (xx: int, yy: Lindgren) {
  xx := var x :| x in {1}; x+10;
  xx := var x :| x in {3, 7, 11}; x+10;
  xx := var x :| x in {n + 12}; x+10;
  yy := var y :| y in {HerrNilsson}; y;
  yy := var y :| y == y; y;
  xx := var x :| x in multiset{3, 3, 2, 3}; x+10;
  xx := var x :| x in map[5 := 10, 6 := 12]; x+10;
  xx := var x :| x in [n, n, 2]; x+10;
  xx := var x :| x in (var m : map<int,int> := map[]; m); x+10;  // error
}

// ------------- ghost loops only modify ghost fields

class GT {
  var x: int;
  var y: int;
  ghost var z: int;
  method M0(N: int)
    modifies this;
  {
    x := 18;
    var n := 0;
    while n < 100 {  // not a ghost loop
      n, y := n + 1, y + 1;
    }
    assert x == 18;  // error: the verifier loses this information for the loop
  }
  method M1(ghost N: int)
    modifies this;
  {
    x := 18;
    ghost var n := N;
    while n < 100 {  // a ghost loop
      n, z := n + 1, z + 1;
    }
    assert x == 18;  // fine, the verifier knows that the loop modifies only ghost state
  }
  method P0()
    modifies this;
  ghost method P1()
    modifies this;
  method Q()
    modifies this;
  {
    if (*) {
      P0();
      assert forall x: GT {:nowarn} :: allocated(x) ==> old(allocated(x));  // error: method P0 may have allocated stuff
    } else {
      P1();
      assert forall x: GT {:nowarn} :: allocated(x) ==> old(allocated(x));  // error: ghost method P1 may have allocated stuff
    }
  }
}

// ----- tests of various ways to express that a collection is nonempty, showing that these all lead to being
// ----- able to pick an element from the (domain of the) collection

module GenericPick {
  function SetPick0<U>(s: set<U>): U
    requires s != {}
  {
    var x :| x in s; x
  }
  function SetPick1<U>(s: set<U>): U
    requires |s| != 0
  {
    var x :| x in s; x
  }
  function SetPick2<U>(s: set<U>): U
    requires exists x :: x in s
  {
    var x :| x in s; x
  }

  function MultisetPick0<U>(s: multiset<U>): U
    requires s != multiset{}
  {
    var x :| x in s; x
  }
  function MultisetPick1<U>(s: multiset<U>): U
    requires |s| != 0
  {
    var x :| x in s; x
  }
  function MultisetPick2<U>(s: multiset<U>): U
    requires exists x :: x in s
  {
    var x :| x in s; x
  }
  function MultisetPick3<U>(s: multiset<U>): U
    requires exists x :: s[x] > 0
  {
    var x :| x in s; x
  }

  function SeqPick0<U>(s: seq<U>): U
    requires s != []
  {
    EquivalentWaysOfSayingSequenceIsNonempty(s);  // I wish this wasn't needed; see comment near Seq#Length axioms in DafnyPrelude.bpl
    var x :| x in s; x
  }
  function SeqPick1<U>(s: seq<U>): U
    requires |s| != 0
  {
    EquivalentWaysOfSayingSequenceIsNonempty(s);  // I wish this wasn't needed; see comment near Seq#Length axioms in DafnyPrelude.bpl
    var x :| x in s; x
  }
  function SeqPick2<U>(s: seq<U>): U
    requires exists x :: x in s
  {
    var x :| x in s; x
  }
  function SeqPick3<U>(s: seq<U>): U
    requires exists i {:nowarn} :: 0 <= i < |s|
  {
    EquivalentWaysOfSayingSequenceIsNonempty(s);  // I wish this wasn't needed; see comment near Seq#Length axioms in DafnyPrelude.bpl
    var x :| x in s; x
  }
  function SeqPick4<U>(s: seq<U>): U
    requires exists i {:nowarn} :: 0 <= i < |s|
  {
    var i :| 0 <= i < |s|; s[i]
  }
  lemma EquivalentWaysOfSayingSequenceIsNonempty<U>(s: seq<U>)
    requires s != []
          || |s| != 0
          || exists i {:nowarn} :: 0 <= i < |s|
    ensures exists x :: x in s
  {
    assert s[0] in s;
  }

  function MapPick0<U,V>(m: map<U,V>): U
    requires m != map[]
  {
    var x :| x in m; x
  }
  function MapPick1<U,V>(m: map<U,V>): U
    requires |m| != 0
  {
    var x :| x in m; x
  }
  function MapPick2<U,V>(m: map<U,V>): U
    requires exists x :: x in m
  {
    var x :| x in m; x
  }
}

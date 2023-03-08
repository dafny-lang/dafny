// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class C {
  var n: set<Node?>

  method M(v: Stack)
    //requires v != null
  {
    var n': set<object?> := n;
    assert v !in n';  // should be known from the types involved
  }

  method N(v: Stack?)
    /* this time with the possibility of "v" being null */
  {
    var n': set<object?> := n;
    assert v !in n';  // error: v may be null
  }

  method A0(a: CP?<int,C>, b: CP?<int,object>)
  {
    var x: object? := a;
    var y: object? := b;
    assert x == y ==> x == null;
  }

  method A1(a: CP?<int,C>)
  {
    var x: object? := a;
    assert forall b: CP?<int,Stack> {:nowarn} :: x == b ==> b == null;  // follows from type antecedents
  }

  var a2x: set<CP?<C,Node>>;
  method A2(b: set<CP?<Node,C>>)
    requires null !in b
  {
    var x: set<object?> := a2x;
    var y: set<object?> := b;
    assert x * y == {};
  }

  method A3(b: set<CP?<Node,C>>)
    /* this time without the precondition */
  {
    var x: set<object?> := a2x;
    var y: set<object?> := b;
    assert x * y <= {null};
  }

  method A4(b: set<CP?<Node,C>>)
    /* again, without the precondition */
  {
    var x: set<object?> := a2x;
    var y: set<object?> := b;
    assert x * y == {};  // error
  }

  method A5()
    decreases *;
  {
    var a := new CP<int,C>;
    var b := new CP<int,object>;
    while (a != null)  // warning: "a" is never null
      decreases *;  // omit loop termination check (in fact, the loop does not terminate)
    {
      var x: object? := a;
      var y: object? := b;
      assert x == y ==> x == null;
      a := a;  // make 'a' a loop target
    }
  }
}

class Stack { }
class Node { }

class CP<T,U> {
}

datatype Data = Lemon | Kiwi(int)

ghost function G(d: Data): int
  requires d != Data.Lemon
{
  match d
  case Lemon => G(d)
  case Kiwi(x) => 7
}

// -------- some things about induction ---------------------------------

datatype Tree<T> = Leaf(T) | Branch(Tree<T>, Tree<T>)

class DatatypeInduction<T(!new)> {
  ghost function LeafCount<G>(tree: Tree<G>): int
  {
    match tree
    case Leaf(t) => 1
    case Branch(left, right) => LeafCount(left) + LeafCount(right)
  }

  method Theorem0(tree: Tree<T>)
    ensures 1 <= LeafCount(tree)
  {
    assert forall t: Tree<T> {:induction} :: 1 <= LeafCount(t);
  }

  // also make sure it works for an instantiated generic datatype
  method Theorem1(bt: Tree<bool>, it: Tree<int>)
    ensures 1 <= LeafCount(bt)
    ensures 1 <= LeafCount(it)
  {
    assert forall t: Tree<bool> {:induction} :: 1 <= LeafCount(t);
    assert forall t: Tree<int> {:induction} :: 1 <= LeafCount(t);
  }

  method NotATheorem0(tree: Tree<T>)
    ensures LeafCount(tree) % 2 == 1
  {
    assert forall t: Tree<T> {:induction} :: LeafCount(t) % 2 == 1;  // error: fails for Branch case
  }

  method NotATheorem1(tree: Tree<T>)
    ensures 2 <= LeafCount(tree)
  {
    assert forall t: Tree<T> {:induction} :: 2 <= LeafCount(t);  // error: fails for Leaf case
  }

  ghost function Predicate(): bool
  {
    forall t: Tree<T> {:induction} :: 2 <= LeafCount(t)
  }

  method NotATheorem2()
  {
    assert Predicate();  // error (this tests Related Location for induction via a predicate)
  }

  // ----- here is a test for induction over integers

  method IntegerInduction_Succeeds(a: array<int>)
    requires a.Length == 0 || a[0] == 0
    requires forall j {:nowarn} {:matchinglooprewrite false} :: 1 <= j < a.Length ==> a[j] == a[j-1]+2*j-1 // WISH: If induction was more powerful, we wouldn't need to rely on the quantifier to produce the j-1 term.
  {
    // The following assertion can be proved by induction:
    assert forall n {:induction} :: 0 <= n < a.Length ==> a[n] == n*n;
  }

  method IntegerInduction_Fails(a: array<int>)
    requires a.Length == 0 || a[0] == 0
    requires forall j :: 1 <= j < a.Length ==> a[j] == a[j-1]+2*j-1 // WISH: Same as above
  {
    // ...but the induction heuristics don't recognize the situation as one where
    // applying induction would be profitable:
    assert forall n :: 0 <= n < a.Length ==> a[n] == n*n;  // error reported
  }
}

// --- opaque types with type parameters ---

abstract module OpaqueTypesWithParameters {
  type P<A>

  method M<B>(p: P<B>, it: P<int>) returns (q: P<B>)
  {
    q := p;
    var a := new P<int>[500](_ => it);
  }

  method DifferentTypes(a: array<P<int>>, b: array<P<bool>>)
    // If P were a known type, then it would also be known that P<int> and P<bool>
    // would be different types, and then the types of 'a' and 'b' would be different,
    // which would imply that the following postcondition would hold.
    // However, it is NOT necessarily the case that the type parameters of an opaque
    // type actually make the opaque type different.  For example, see the refinement
    // module CaseInPoint below.
    ensures a != b;  // error
  {
  }
}

module CaseInPoint refines OpaqueTypesWithParameters {
  type P<A> = real  // note, the type parameter is not used
  method Client() {
    var x := new real[100];
    DifferentTypes(x, x);
    assert false;  // this is provable here, since DifferentTypes has a bogus postcondition
  }
}

module SomeTypeInferenceTests {
  class MyClass {
    constructor ()
  }

  class Cell<G> {
    var data: G
    constructor (g: G) {
      data := g;
    }
  }

  // The following methods test type inference.  To see that type inference did the
  // right thing, we could use /rprint:- for this test file.  However, that also
  // prints a bunch of other things that we don't care to test here.  So, instead
  // we do some comparisons against "null" and see whether or not they produce
  // null-redundancy warnings.

  method Test0() {
    var m := new MyClass();
    var b := new Cell(m);
    var test;
    test := m == null;  // warning
    test := b == null;  // warning
  }

  method Test1() {
    var m := new MyClass();
    var c := new Cell<MyClass>(m);
    var test;
    test := m == null;  // warning
    test := c == null;  // warning
  }

  method Test2() {
    var m := new MyClass();
    var c := new Cell<MyClass>(m);
    var d: Cell<MyClass> := c;
    var test;
    test := m == null;  // warning
    test := c == null;  // warning
    test := d == null;  // warning
  }
}

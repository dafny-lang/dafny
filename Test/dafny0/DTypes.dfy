class C {
  var n: set<Node>;

  method M(v: Stack)
    requires v != null;
  {
    var o: object := v;
    assert o !in n;  // should be known from the types involved
  }

  method N(v: Stack)
    /* this time without the precondition */
  {
    var o: object := v;
    assert o !in n;  // error: v may be null
  }

  method A0(a: CP<int,C>, b: CP<int,object>)
  {
    var x: object := a;
    var y: object := b;
    assert x == y ==> x == null;
  }

  method A1(a: CP<int,C>)
  {
    var x: object := a;
    assert (forall b: CP<int,Stack> :: x == b ==> b == null);  // follows from type antecedents
  }

  var a2x: set<CP<C,Node>>;
  method A2(b: set<CP<Node,C>>)
    requires null !in b;
  {
    var x: set<object> := a2x;
    var y: set<object> := b;
    assert x * y == {};
  }

  method A3(b: set<CP<Node,C>>)
    /* this time without the precondition */
  {
    var x: set<object> := a2x;
    var y: set<object> := b;
    assert x * y <= {null};
  }

  method A4(b: set<CP<Node,C>>)
    /* again, without the precondition */
  {
    var x: set<object> := a2x;
    var y: set<object> := b;
    assert x * y == {};  // error
  }

  method A5()
  {
    var a := new CP<int,C>;
    var b := new CP<int,object>;
    while (a != null)
      decreases *;  // omit loop termination check (in fact, the loop does not terminate)
    {
      var x: object := a;
      var y: object := b;
      assert x == y ==> x == null;
      a := a;  // make 'a' a loop target
    }
  }
}

class Stack { }
class Node { }

class CP<T,U> {
}

datatype Data = Lemon | Kiwi(int);

function G(d: Data): int
  requires d != Data.Lemon;
{
  match d
  case Lemon => G(d)
  case Kiwi(x) => 7
}

// -------- some things about induction ---------------------------------

datatype Tree<T> = Leaf(T) | Branch(Tree<T>, Tree<T>);

class DatatypeInduction<T> {
  function LeafCount<G>(tree: Tree<G>): int
  {
    match tree
    case Leaf(t) => 1
    case Branch(left, right) => LeafCount(left) + LeafCount(right)
  }

  method Theorem0(tree: Tree<T>)
    ensures 1 <= LeafCount(tree);
  {
    assert (forall t: Tree<T> :: 1 <= LeafCount(t));
  }

  // also make sure it works for an instantiated generic datatype
  method Theorem1(bt: Tree<bool>, it: Tree<int>)
    ensures 1 <= LeafCount(bt);
    ensures 1 <= LeafCount(it);
  {
    assert (forall t: Tree<bool> :: 1 <= LeafCount(t));
    assert (forall t: Tree<int> :: 1 <= LeafCount(t));
  }

  method NotATheorem0(tree: Tree<T>)
    ensures LeafCount(tree) % 2 == 1;
  {
    assert (forall t: Tree<T> :: LeafCount(t) % 2 == 1);  // error: fails for Branch case
  }

  method NotATheorem1(tree: Tree<T>)
    ensures 2 <= LeafCount(tree);
  {
    assert (forall t: Tree<T> :: 2 <= LeafCount(t));  // error: fails for Leaf case
  }

  function Predicate(): bool
  {
    (forall t: Tree<T> :: 2 <= LeafCount(t))
  }

  method NotATheorem2()
  {
    assert Predicate();  // error (this tests Related Location for induction via a predicate)
  }

  // ----- here is a test for induction over integers

  method IntegerInduction_Succeeds(a: array<int>)
    requires a != null;
    requires a.Length == 0 || a[0] == 0;
    requires forall j :: 1 <= j && j < a.Length ==> a[j] == a[j-1]+2*j-1;
  {
    // The following assertion can be proved by induction:
    assert forall n {:induction} :: 0 <= n && n < a.Length ==> a[n] == n*n;
  }

  method IntegerInduction_Fails(a: array<int>)
    requires a != null;
    requires a.Length == 0 || a[0] == 0;
    requires forall j :: 1 <= j && j < a.Length ==> a[j] == a[j-1]+2*j-1;
  {
    // ...but the induction heuristics don't recognize the situation as one where
    // applying induction would be profitable:
    assert forall n :: 0 <= n && n < a.Length ==> a[n] == n*n;  // error reported
  }
}

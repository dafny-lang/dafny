// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Termination {
  method A(N: int)
    requires 0 <= N;
  {
    var i := 0;
    while (i < N)
      invariant i <= N;
      // this will be heuristically inferred:  decreases N - i;
    {
      i := i + 1;
    }
  }

  method B(N: int)
    requires 0 <= N;
  {
    var i := N;
    while (true)
      invariant 0 <= i;
      decreases i;
    {
      i := i - 1;
      if (!(0 <= i)) {
        break;
      }
    }
    assert i == -1;
  }

  method Lex() {
    var x := Update();
    var y := Update();
    while (!(x == 0 && y == 0))
      invariant 0 <= x && 0 <= y;
      decreases x, y;
    {
      if (0 < y) {
        y := y - 1;
      } else {
        x := x - 1;
        y := Update();
      }
    }
  }

  method Update() returns (r: int)
    ensures 0 <= r;
  {
    r := 8;
  }

  method M() {
    var b := true;
    var i := 500;
    var r := new Termination;
    var s := {12, 200};
    var q := [5, 8, 13];
    while (true)
      decreases b, i, r;
//      invariant b ==> 0 <= i;
      decreases s, q;
    {
      if (12 in s) {
        s := s - {12};
      } else if (b) {
        b := !b;
        i := i + 1;
      } else if (20 <= i) {
        i := i - 20;
      } else if (r != null) {
        r := null;
      } else if (|q| != 0) {
        q := q[1..];
      } else {
        break;
      }
    }
  }

  method Q<T>(list: List<T>) {
    var l := list;
    while (l != List.Nil)
      decreases l;
    {
      var x;
      x, l := Traverse(l);
    }
  }

  method Traverse<T>(a: List<T>) returns (val: T, b: List<T>)
    requires a != List.Nil;
    ensures a == List.Cons(val, b);
  {
    match a {
      case Cons(v, r) => val := v; b := r;
    }
  }
}

datatype List<T> = Nil | Cons(T, List<T>)

method FailureToProveTermination0(N: int)
{
  var n := N;
  while (n < 100) {  // error: may not terminate
    n := n - 1;
  }
}

method FailureToProveTermination1(x: int, y: int, N: int)
{
  var n := N;
  while (x < y && n < 100)  // error: cannot prove termination from the heuristically chosen termination metric
  {
    n := n + 1;
  }
}

method FailureToProveTermination2(x: int, y: int, N: int)
{
  var n := N;
  while (x < y && n < 100)  // error: cannot prove termination from the given (bad) termination metric
    decreases n - x;
  {
    n := n + 1;
  }
}

method FailureToProveTermination3(x: int, y: int, N: int)
{
  var n := N;
  while (x < y && n < 100)
    decreases 100 - n;
  {
    n := n + 1;
  }
}

method FailureToProveTermination4(x: int, y: int, N: int)
{
  var n := N;
  while (n < 100 && x < y)
    decreases 100 - n;
  {
    n := n + 1;
  }
}

method FailureToProveTermination5(b: bool, N: int)
{
  var n := N;
  while (b && n < 100)  // here, the heuristics are good enough to prove termination
  {
    n := n + 1;
  }
}

class Node {
  var next: Node?;
  var footprint: set<Node?>;

  function Valid(): bool
    reads this, footprint;
    // In a previous (and weaker) axiomatization of sets, there had been two problems
    // with trying to prove the termination of this function.  First, the default
    // decreases clause (derived from the reads clause) had been done incorrectly for
    // a list of expressions.  Second, the set axiomatization had not been strong enough.
  {
    this in footprint && !(null in footprint) &&
    (next != null  ==>  next in footprint &&
                        next.footprint < footprint &&
                        this !in next.footprint &&
                        next.Valid())
  }
}

method DecreasesYieldsAnInvariant(z: int) {
  var x := 100;
  var y := 1;
  var z := z;  // make parameter into a local variable
  while (x != y)
    // inferred: decreases |x - y|;
    invariant  (0 < x && 0 < y) || (x < 0 && y < 0);
  {
    if (z == 52) {
      break;
    } else if (x < y) {
      y := y - 1;
    } else {
      x := x - 1;
    }
    x := -x;
    y := -y;
    z := z + 1;
  }
  assert x - y < 100;  // follows from the fact that no loop iteration increases what's in the 'decreases' clause
}

// ----------------------- top elements --------------------------------------

class TopElements {
  var count: int;

  // Here is the old way that this had to be specified:

  method OuterOld(a: int)
    modifies this;
    decreases a, true;
  {
    count := count + 1;
    InnerOld(a, count);
  }

  method InnerOld(a: int, b: int)
    modifies this;
    decreases a, false, b;
  {
    count := count + 1;
    if (b == 0 && 1 <= a) {
      OuterOld(a - 1);
    } else if (1 <= b) {
      InnerOld(a, b - 1);
    }
  }

  // Now the default specifications ("decreases a;" and "decreases a, b;") suffice:

  method Outer(a: int)
    modifies this;
  {
    count := count + 1;
    Inner(a, count);
  }

  method Inner(a: int, b: int)
    modifies this;
  {
    count := count + 1;
    if (b == 0 && 1 <= a) {
      Outer(a - 1);
    } else if (1 <= b) {
      Inner(a, b - 1);
    }
  }
}
// -------------------------- decrease either datatype value -----------------

function Zipper0<T>(a: List<T>, b: List<T>): List<T>
{
  match a
  case Nil => b
  case Cons(x, c) => List.Cons(x, Zipper0(b, c))  // error: cannot prove termination
}

function Zipper1<T>(a: List<T>, b: List<T>, k: bool): List<T>
  decreases if k then a else b, if k then b else a;
{
  match a
  case Nil => b
  case Cons(x, c) => List.Cons(x, Zipper1(b, c, !k))
}

function Zipper2<T>(a: List<T>, b: List<T>): List<T>
  decreases /* max(a,b) */ if a < b then b else a,
            /* min(a,b) */ if a < b then a else b;
{
  match a
  case Nil => b
  case Cons(x, c) => List.Cons(x, Zipper2(b, c))
}

// -------------------------- test translation of while (*) -----------------

method WhileStar0(n: int)
  requires 2 <= n;
  decreases *;
{
  var m := n;
  var k := 0;
  while (*)
    invariant 0 <= k && 0 <= m;
    decreases *;
  {
    k := k + m;
    m := m + k;
  }
  assert 0 <= k;
}

method WhileStar1()
{
  var k := 0;
  while (*)  // error: failure to prove termination
  {
    k := k + 1;
    if (k == 17) { break; }
  }
}

method WhileStar2()
{
  var k := 0;
  while (*)
    invariant k < 17;
    decreases 17 - k;
  {
    k := k + 1;
    if (k == 17) { break; }
  }
}

// -----------------

function ReachBack(n: int): bool
  requires 0 <= n;
  ensures ReachBack(n);
{
  // Turn off induction for this test, since that's not the point of
  // the test case.
  (forall m {:induction false} :: 0 <= m && m < n ==> ReachBack(m))
}

function ReachBack_Alt(n: int): bool
  requires 0 <= n;
{
  n == 0 || ReachBack_Alt(n-1)
}

ghost method Lemma_ReachBack()
{
  assert (forall m :: 0 <= m ==> ReachBack_Alt(m));
}

// ----------------- default decreases clause for functions ----------

class DefaultDecreasesFunction {
  var data: int;
  ghost var Repr: set<object?>;
  var next: DefaultDecreasesFunction?;
  predicate Valid()
    reads this, Repr;
  {
    this in Repr && null !in Repr &&
    (next != null ==> next in Repr && next.Repr <= Repr && this !in next.Repr && next.Valid())
  }
  function F(x: int): int
    requires Valid();
    reads this, Repr;
    // the default reads clause is: decreases Repr, x
  {
    if next == null || x < 0 then x else next.F(x + data)
  }
  function G(x: int): int
    requires Valid();
    reads this, Repr;
    decreases x;
  {
    if next == null || x < 0 then x else next.G(x + data)  // error: failure to reduce 'decreases' measure
  }
  function H(x: int): int
    requires Valid() && 0 <= x;
    reads this, Repr;
    // the default reads clause is: decreases Repr, x
  {
    if next != null then
      next.H(Abs(data))  // this recursive call decreases Repr
    else if x < 78 then
      data + x
    else
      H(x - 1)  // this recursive call decreases x
  }
  function Abs(x: int): int
  {
    if x < 0 then -x else x
  }
}

// ----------------- multisets and maps ----------

module MultisetTests {
  function F(a: multiset<int>, n: nat): int
    decreases a, n;
  {
    if n == 0 then 0 else F(a, n-1)
  }

  function F'(a: multiset<int>, n: nat): int  // inferred decreases clause
  {
    if n == 0 then 0 else F'(a, n-1)
  }

  ghost method M(n: nat, b: multiset<int>)
    ensures F(b, n) == 0;  // proved via automatic induction
  {
  }
}

module MapTests {
  function F(a: map<int,int>, n: nat): int
    decreases a, n;
  {
    if n == 0 then 0 else F(a, n-1)
  }

  function F'(a: map<int,int>, n: nat): int  // inferred decreases clause
  {
    if n == 0 then 0 else F'(a, n-1)
  }

  ghost method M(n: nat, b: map<int,int>)
    ensures F(b, n) == 0;  // proved via automatic induction
  {
  }
}

// --------------------- The following regression test case relies on the previous rank
// --------------------- really being evaluated in the initial state

class C {
  var v: nat;
  method Terminate()
    modifies this;
    decreases v;
  {
    if (v != 0) {
      v := v - 1;
      Terminate();
    }
  }
}

// --------------------- decreases * tests

module TerminationRefinement0 {
  method M(x: int)
    decreases *;
  {
    M(x);  // error [in TerminationRefinement1]: bad recursion
           // Note, no complaint is issued in TerminationRefinement0, since
           // the method is declared with 'decreases *'.
  }
}
module TerminationRefinement1 refines TerminationRefinement0 {
  method M...
    decreases 4;  // this will cause termination checking to be done, and it will produce an error message for the recursive call
  {
    ...;
  }
}

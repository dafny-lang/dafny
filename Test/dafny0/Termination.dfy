// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Termination {
  method A(N: int)
    requires 0 <= N
  {
    var i := 0;
    while i < N
      invariant i <= N
      // this will be heuristically inferred:  decreases N - i
    {
      i := i + 1;
    }
  }

  method B(N: int)
    requires 0 <= N
  {
    var i := N;
    while true
      invariant 0 <= i
      decreases i
    {
      i := i - 1;
      if !(0 <= i) {
        break;
      }
    }
    assert i == -1;
  }

  method Lex() {
    var x := Update();
    var y := Update();
    while !(x == 0 && y == 0)
      invariant 0 <= x && 0 <= y
      decreases x, y
    {
      if 0 < y {
        y := y - 1;
      } else {
        x := x - 1;
        y := Update();
      }
    }
  }

  method Update() returns (r: int)
    ensures 0 <= r
  {
    r := 8;
  }

  method M() {
    var b := true;
    var i := 500;
    var r := new Termination;
    var s := {12, 200};
    var q := [5, 8, 13];
    while true
      decreases b, i, r
//      invariant b ==> 0 <= i
      decreases s, q
    {
      if 12 in s {
        s := s - {12};
      } else if b {
        b := !b;
        i := i + 1;
      } else if 20 <= i {
        i := i - 20;
      } else if r != null {
        r := null;
      } else if |q| != 0 {
        q := q[1..];
      } else {
        break;
      }
    }
  }

  method Q<T>(list: List<T>) {
    var l := list;
    while l != List.Nil
      decreases l
    {
      var x;
      x, l := Traverse(l);
    }
  }

  method Traverse<T>(a: List<T>) returns (val: T, b: List<T>)
    requires a != List.Nil
    ensures a == List.Cons(val, b)
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
  while n < 100 {  // error: may not terminate
    n := n - 1;
  }
}

method ImprovedHeuristicsMakeThisVerify(x: int, y: int, N: int)
{ // when auto-decreases used only one expression, this failed to prove termination, but now it works!
  var n := N;
  while x < y && n < 100
  {
    n := n + 1;
  }
}

method FailureToProveTermination2(x: int, y: int, N: int)
{
  var n := N;
  while x < y && n < 100  // error: cannot prove termination from the given (bad) termination metric
    decreases n - x
  {
    n := n + 1;
  }
}

method FailureToProveTermination3(x: int, y: int, N: int)
{
  var n := N;
  while x < y && n < 100
    decreases 100 - n
  {
    n := n + 1;
  }
}

method FailureToProveTermination4(x: int, y: int, N: int)
{
  var n := N;
  while n < 100 && x < y
    decreases 100 - n
  {
    n := n + 1;
  }
}

method FailureToProveTermination5(b: bool, N: int)
{
  var n := N;
  while b && n < 100  // here, the heuristics are good enough to prove termination
  {
    n := n + 1;
  }
}

class Node {
  var next: Node?
  var footprint: set<Node?>

  ghost function Valid(): bool
    reads this, footprint
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
  while x != y
    // inferred: decreases |x - y|
    invariant  (0 < x && 0 < y) || (x < 0 && y < 0)
  {
    if z == 52 {
      break;
    } else if x < y {
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
  var count: int

  // Here is the old way that this had to be specified:

  method OuterOld(a: int)
    modifies this
    decreases a, true
  {
    count := count + 1;
    InnerOld(a, count);
  }

  method InnerOld(a: int, b: int)
    modifies this
    decreases a, false, b
  {
    count := count + 1;
    if b == 0 && 1 <= a {
      OuterOld(a - 1);
    } else if 1 <= b {
      InnerOld(a, b - 1);
    }
  }

  // Now the default specifications ("decreases a" and "decreases a, b") suffice:

  method Outer(a: int)
    modifies this
  {
    count := count + 1;
    Inner(a, count);
  }

  method Inner(a: int, b: int)
    modifies this
  {
    count := count + 1;
    if b == 0 && 1 <= a {
      Outer(a - 1);
    } else if 1 <= b {
      Inner(a, b - 1);
    }
  }
}
// -------------------------- decrease either datatype value -----------------

ghost function Zipper0<T>(a: List<T>, b: List<T>): List<T>
{
  match a
  case Nil => b
  case Cons(x, c) => List.Cons(x, Zipper0(b, c))  // error: cannot prove termination
}

ghost function Zipper1<T>(a: List<T>, b: List<T>, k: bool): List<T>
  decreases if k then a else b, if k then b else a
{
  match a
  case Nil => b
  case Cons(x, c) => List.Cons(x, Zipper1(b, c, !k))
}

ghost function Zipper2<T>(a: List<T>, b: List<T>): List<T>
  decreases /* max(a,b) */ if a < b then b else a,
            /* min(a,b) */ if a < b then a else b
{
  match a
  case Nil => b
  case Cons(x, c) => List.Cons(x, Zipper2(b, c))
}

// -------------------------- test translation of while * -----------------

method WhileStar0(n: int)
  requires 2 <= n
  decreases *
{
  var m := n;
  var k := 0;
  while *
    invariant 0 <= k && 0 <= m
    decreases *
  {
    k := k + m;
    m := m + k;
  }
  assert 0 <= k;
}

method WhileStar1()
{
  var k := 0;
  while *  // error: failure to prove termination
  {
    k := k + 1;
    if k == 17 { break; }
  }
}

method WhileStar2()
{
  var k := 0;
  while *
    invariant k < 17
    decreases 17 - k
  {
    k := k + 1;
    if k == 17 { break; }
  }
}

// -----------------

ghost function ReachBack(n: int): bool
  requires 0 <= n
  ensures ReachBack(n)
{
  // Turn off induction for this test, since that's not the point of
  // the test case.
  forall m {:induction false} :: 0 <= m && m < n ==> ReachBack(m)
}

ghost function ReachBack_Alt(n: int): bool
  requires 0 <= n
{
  n == 0 || ReachBack_Alt(n-1)
}

ghost method Lemma_ReachBack()
{
  assert forall m {:induction} :: 0 <= m ==> ReachBack_Alt(m);
}

// ----------------- default decreases clause for functions ----------

class DefaultDecreasesFunction {
  var data: int
  ghost var Repr: set<object?>
  var next: DefaultDecreasesFunction?
  ghost predicate Valid()
    reads this, Repr
  {
    this in Repr && null !in Repr &&
    (next != null ==> next in Repr && next.Repr <= Repr && this !in next.Repr && next.Valid())
  }
  ghost function F(x: int): int
    requires Valid()
    reads this, Repr
    // the default reads clause is: decreases Repr, x
  {
    if next == null || x < 0 then x else next.F(x + data)
  }
  ghost function G(x: int): int
    requires Valid()
    reads this, Repr
    decreases x
  {
    if next == null || x < 0 then x else next.G(x + data)  // error: failure to reduce 'decreases' measure
  }
  ghost function H(x: int): int
    requires Valid() && 0 <= x
    reads this, Repr
    // the default reads clause is: decreases Repr, x
  {
    if next != null then
      next.H(Abs(data))  // this recursive call decreases Repr
    else if x < 78 then
      data + x
    else
      H(x - 1)  // this recursive call decreases x
  }
  ghost function Abs(x: int): int
  {
    if x < 0 then -x else x
  }
}

// ----------------- multisets and maps ----------

module MultisetTests {
  ghost function F(a: multiset<int>, n: nat): int
    decreases a, n
  {
    if n == 0 then 0 else F(a, n-1)
  }

  ghost function F'(a: multiset<int>, n: nat): int  // inferred decreases clause
  {
    if n == 0 then 0 else F'(a, n-1)
  }

  ghost method M(n: nat, b: multiset<int>)
    ensures F(b, n) == 0  // proved via automatic induction
  {
  }
}

module MapTests {
  ghost function F(a: map<int,int>, n: nat): int
    decreases a, n
  {
    if n == 0 then 0 else F(a, n-1)
  }

  ghost function F'(a: map<int,int>, n: nat): int  // inferred decreases clause
  {
    if n == 0 then 0 else F'(a, n-1)
  }

  ghost method M(n: nat, b: map<int,int>)
    ensures F(b, n) == 0  // proved via automatic induction
  {
  }
}

// --------------------- The following regression test case relies on the previous rank
// --------------------- really being evaluated in the initial state

class C {
  var v: nat
  method Terminate()
    modifies this
    decreases v
  {
    if v != 0 {
      v := v - 1;
      Terminate();
    }
  }
}

// --------------------- decreases * tests

module TerminationRefinement0 {
  method M(x: int)
    decreases *
  {
    M(x);  // error [in TerminationRefinement1]: bad recursion
           // Note, no complaint is issued in TerminationRefinement0, since
           // the method is declared with 'decreases *'.
  }
}
module TerminationRefinement1 refines TerminationRefinement0 {
  method M...
    decreases 4  // this will cause termination checking to be done, and it will produce an error message for the recursive call
  {
    ...;
  }
}

// --------------------- Include "this" for members of types where the ordering makes sense

datatype Tree = Empty | Node(root: int, left: Tree, right: Tree)
{
  ghost function Elements(): set<int>
    // auto: decreases this
  {
    match this
    case Empty => {}
    case Node(x, left, right) => {x} + left.Elements() + right.Elements()
  }

  ghost function Sum(): int
    // auto: decreases this
  {
    match this
    case Empty => 0
    case Node(x, left, right) => x + left.Sum() + right.Sum()
  }

  method ComputeSum(n: nat) returns (s: int)
    // auto: decreases this, n
  {
    match this
    case Empty =>
      return 0;
    case Node(x, left, right) =>
      if n == 0 {
        var l := left.ComputeSum(28);
        var r := right.ComputeSum(19);
        return x + l + r;
      } else {
        s := ComputeSum(n - 1);
      }
  }

  lemma {:induction this} EvensSumToEven()  // explicitly use "this" as quantified over by induction hypothesis
    requires forall u :: u in Elements() ==> u % 2 == 0
    ensures Sum() % 2 == 0
    // auto: decreases this
  {
    match this
    case Empty =>
    case Node(x, left, right) =>
      assert x in Elements();
      left.EvensSumToEven();
      right.EvensSumToEven();
  }

  lemma EvensSumToEvenAutoInduction()  // {:induction this} is the default
    requires forall u :: u in Elements() ==> u % 2 == 0
    ensures Sum() % 2 == 0
    // auto: decreases this
  {
    match this
    case Empty =>
    case Node(x, left, right) =>
      assert x in Elements();
      left.EvensSumToEvenAutoInduction();
      right.EvensSumToEvenAutoInduction();
  }
}

lemma ExtEvensSumToEven(t: Tree)
  requires forall u :: u in t.Elements() ==> u % 2 == 0
  ensures t.Sum() % 2 == 0
  // auto: decreases t
{
  match t
  case Empty =>
  case Node(x, left, right) =>
    assert x in t.Elements();
    assert left.Sum() % 2 == 0;
    assert right.Sum() % 2 == 0;
    assert t.Sum() % 2 == 0;
}

// ------ attempts to use a decreases term whose "less" relation is "false"

method LoopyInt(x: int) {
  while x < 100  // error: failure to decreases termination metric
    decreases 58
  {
  }
}

method LoopyISet(m: imap<int, int>)
{
  while m != imap[]  // error: failure to decreases termination metric
    decreases m.Keys
  {
  }
}

method LoopyIMap(x: int, m: imap<int, int>) {
  while x < 100  // error: failure to decreases termination metric
    decreases m
  {
  }
}

method LoopyFunction(x: int, f: int -> int) {
  while x < 100  // error: failure to decreases termination metric
    decreases f
  {
  }
}

method LoopyTypeParam<Y>(x: int, y: Y) {
  while x < 100  // error: failure to decreases termination metric
    decreases y
  {
  }
}

type ZOT
method LoopyOpaqueType(x: int, z: ZOT) {
  while x < 100  // error: failure to decreases termination metric
    decreases z
  {
  }
}

type SubZOT = z: ZOT | true  // error: cannot find witness
method LoopySubsetType(x: int, z: SubZOT) {
  while x < 100  // error: failure to decreases termination metric
    decreases z
  {
  }
}

codatatype Forever = More(next: Forever)

method LoopyForever(x: int, f: Forever) {
  var f := f;
  while x < 100  // error: failure to decreases termination metric
    decreases f
  {
    f := f.next;
  }
}

method GoodLoop<Y>(x: int, y: Y, z0: ZOT, z1: SubZOT, f: int -> int, forever: Forever, m: imap<int, int>, s: iset<int>)
{
  var i := 0;
  while i < x
    decreases y, z0, z1, f, forever, m, s, x - i
  {
    i := i + 1;
  }
}

// ------------------ sets -----------------------

method Sets0(S: set) {
  var s := S;
  while s != {} {
    var x :| x in s;
    s := s - {x};
  }
}

method Sets1(S: set) {
  var s := S;
  while {} != s {
    var x :| x in s;
    s := s - {x};
  }
}

method Sets2(S: set) {
  var s := S;
  while {} < s {
    var x :| x in s;
    s := s - {x};
  }
}

method Sets3(S: set) {
  var s := S;
  while s > {} {
    var x :| x in s;
    s := s - {x};
  }
}

method SetsST0<Y>(S: set, y: Y) {
  var s := S;
  var t := {y};
  while t < s {
    var x :| x in s && x != y;
    s := s - {x};
  }
}

method SetsST1<Y>(S: set, y: Y) {
  var s := S;
  var t := {y};
  while t <= s {
    var x :| x in s && (x != y || s == t);
    s := s - {x};
    if s == {} { break; }
  }
}

method SetsST2<Y>(S: set, y: Y) {
  var s := S;
  var t := {y};
  while s != t && s != {} {
    var x :| x in s;
    if x == y { break; }
    s := s - {x};
  }
}

method SetsST3<Y>(S: set, y: Y)
  requires y in S
{
  var s := S;
  var t := {y};
  while s != t // error: cannot prove termination
    invariant t <= s
  {
    var x :| x in s;
    s := s - {x};
  }
}

method SetsST4<Y>(S: set, y: Y)
  requires y in S
{
  var s := S;
  var t := {y};
  while s != t
    invariant t <= s
  {
    var x :| x in s && x != y;
    s := s - {x};
  }
}

method SetsST5<Y>(S: set, y: Y, P: set)
  requires y in S && P != {} && S !! P
{
  var s := S;
  var t := {y};
  while s != t
    invariant s * P <= t <= s && y in t
  {
    var z :| z in P;
    assert s - t == (s + {z}) - (t + {z});
    s, t := s + {z}, t + {z};

    var x :| x in s && x !in t;
    s := s - {x};
  }
}

method ISets0(S: iset) {
  var s := S;
  while s != iset{} { // error: cannot prove termination
    var x :| x in s;
    s := s - iset{x};
  }
}

method ISets1(S: iset) {
  var s := S;
  while s > iset{} { // error: cannot prove termination
    var x :| x in s;
    s := s - iset{x};
  }
}

method ISets2(S: iset) {
  var s := S;
  while s != iset{} // error: cannot prove termination
    decreases s // the well-founded relation for an iset is "false"
  {
    var x :| x in s;
    s := s - iset{x};
  }
}

// ------------------ multisets -----------------------

method Multisets0(S: multiset) {
  var s := S;
  while s != multiset{} {
    var x :| x in s;
    s := s - multiset{x};
  }
}

method Multisets1(S: multiset) {
  var s := S;
  while multiset{} != s {
    var x :| x in s;
    s := s - multiset{x};
  }
}

method Multisets2(S: multiset) {
  var s := S;
  while multiset{} < s {
    var x :| x in s;
    s := s - multiset{x};
  }
}

method Multisets3(S: multiset) {
  var s := S;
  while s > multiset{} {
    var x :| x in s;
    s := s - multiset{x};
  }
}

method MultisetsST0<Y>(S: multiset, y: Y) {
  var s := S;
  var t := multiset{y};
  while t < s {
    var x :| x in s && (x != y || 2 <= s[y]); // don't pick the last y
    s := s - multiset{x};
  }
}

method MultisetsST1<Y>(S: multiset, y: Y) {
  var s := S;
  var t := multiset{y};
  while t <= s {
    var x :| x in s && (x != y || 2 <= s[y] || s == t);
    s := s - multiset{x};
    if s == multiset{} { break; }
  }
}

method MultisetsST2<Y>(S: multiset, y: Y) {
  var s := S;
  var t := multiset{y};
  while s != t && s != multiset{} {
    var x :| x in s;
    if x == y { break; }
    s := s - multiset{x};
  }
}

method MultisetsST3<Y>(S: multiset, y: Y)
  requires y in S
{
  var s := S;
  var t := multiset{y};
  while s != t // error: cannot prove termination
    invariant t <= s
  {
    var x :| x in s;
    s := s - multiset{x};
  }
}

method MultisetsST4<Y>(S: multiset, y: Y)
  requires S[y] == 1
{
  var s := S;
  var t := multiset{y};
  while s != t
    invariant t <= s && s[y] <= 1
  {
    var x :| x in s && x != y;
    s := s - multiset{x};
  }
}

method MultisetsST5<Y>(S: multiset, y: Y, P: multiset)
  requires S[y] == 1 && P != multiset{} && S !! P
{
  var s := S;
  var t := multiset{y};
  while s != t
    invariant s * P <= t <= s && s[y] <= t[y]
  {
    var z :| z in P;
    s, t := s + multiset{z}, t + multiset{z};

    var x :| x in s && t[x] < s[x];
    s := s - multiset{x};
  }
}

// ------------------ sequences -----------------------

method Sequences0(S: seq) {
  var s := S;
  while s != [] {
    var i :| 0 <= i < |s|;
    s := s[..i] + s[i + 1..];
  }
}

method Sequences1(S: seq) {
  var s := S;
  while [] != s {
    s := s[1..];
  }
}

method Sequences2<T(==)>(S: seq) {
  var s := S;
  while [] < s {
    s := s[..|s| - 1];
  }
}

method Sequences3<T(==)>(S: seq) {
  var s := S;
  while [] <= s {
    if s == [] { break; }
    s := s[..|s| / 2];
  }
}

method Sequences4(S: seq) {
  var i := 0;
  while S[i..] != []
    invariant 0 <= i <= |S|
  {
    assert S[i + 1..] == S[i..][1..];
    i := i + 1;
  }
}

// ------------------ negations -----------------------

method Negation0(S: set) {
  var s := S;
  while !(s == {}) {
    var x :| x in s;
    s := s - {x};
  }
}

method Negation1(S: set) {
  var s := S;
  while !!(s != {}) {
    var x :| x in s;
    s := s - {x};
  }
}

// ------------------ multiple conjuncts in the guard -----------------------

method MultipleGuardConjuncts0(N: nat) {
  var s, b := N, *;
  while b && s != 0 {
    s, b := s - 1, *;
  }
}

newtype QuitePositive = x | 23 <= x witness 29

method MultipleGuardConjuncts1(N: QuitePositive) {
  var s, b := N, *;
  while b && s != 23 { // decreases if b then AbsDiff(s as int, 23 as int) else -1
    s, b := (s as int - 1) as QuitePositive, *;
  }
}

method MultipleGuardConjuncts2(S: real) {
  var s, b := 0.0, *;
  while b && s < S {
    s := s + 1.0;
  }
}

newtype SoReal = r | 10.0 <= r witness 12.2

method MultipleGuardConjuncts3(S: SoReal) {
  var s, b := 13.0, *;
  while b && s < S { // decreases if b then S as real - s as real else -1.0
    s := s + s;
  }
}

method MultipleGuardConjuncts4(S: set) {
  var s, b := S, *;
  while b && s != {} {
    var x :| x in s;
    s, b := s - {x}, *;
  }
}

method MultipleGuardConjuncts5(S: multiset) {
  var s, b := S, *;
  while b && s != multiset{} {
    var x :| x in s;
    s, b := s - multiset{x}, *;
  }
}

method MultipleGuardConjuncts6(S: seq) {
  var s, b := S, *;
  while b && s != [] {
    assert s[..0] == [];
    s, b := s[1..], true;
  }
}

method LexicographicTuples0(A: int) {
  var a, b := A, *;
  while 0 < a && 0 < b {
    if 0 < b {
      b := b - 1;
    } else {
      a, b := a - 1, *;
    }
  }
}

method LexicographicTuples1(A: int) {
  var a, b := A, *;
  while 0 < a && 10 / a < b {
    if 0 < b {
      b := b - 1;
    } else {
      a, b := a - 1, *;
    }
  }
}

method LexicographicTuples2(A: int) {
  var a, b, c := A, *, *;
  while 0 < a && 0 < b && 0 < c {
    if 0 < c {
      c := c - 1;
    } else if 0 < b {
      b := b - 1;
    } else {
      a, b := a - 1, *;
    }
  }
}

method LexicographicTuples3(A: int) {
  var a, b, c := A, *, *;
  var u, v, w, x, y, z, omega;
  while u && v && 0 < a && w && x && 0 < b && y && z && 0 < c && omega {
    if 0 < c {
      c := c - 1;
    } else if 0 < b {
      b := b - 1;
    } else {
      a, b := a - 1, *;
    }
    u, v, w, x, y, z, omega := *, *, *, *, *, *, *;
  }
}

method NegationNormalForm0(A: nat) {
  var a: nat, b: nat := A, *;
  while !(a == 0 || b == 0) {
    if 0 < b {
      b := b - 1;
    } else {
      a, b := a - 1, *;
    }
  }
}

method NegationNormalForm1(S: set) {
  var s := S;
  while !(s == {}) {
    var x :| x in s;
    s := s - {x};
  }
}

method NegationNormalForm2(S: multiset) {
  var s := S;
  while !(|s| == 0) {
    var x :| x in s;
    s := s - multiset{x};
  }
}

method NegationNormalForm3(S: set, Q: seq, A: nat) {
  var s, q, b, a := S, Q, *, A;
  while !({} < s ==> q != []) && b && !!(a < 1000)  {
    b := *;
    if
    case x :| x in s =>
      s := s - {x};
    case |q| > 0 =>
      q := q[1..];
    case a < 123_456 =>
      a := a + 1;
  }
}

method NegationNormalForm4(S: set, Q: seq, A: nat) {
  var s, q, b, a := S, Q, *, A;
  while !({} < s ==> !(q != [])) && b && !!(a < 1000)  {
    b := *;
    if
    case x :| x in s =>
      s := s - {x};
    case |q| > 0 =>
      q := q[1..];
    case a < 123_456 =>
      a := a + 1;
  }
}

// -------- some other types -----------

method Bitvectors0(A: bv3, B: bv3) {
  var a, b := A, B;
  while a < b {
    if * {
      b := b - 1;
    } else {
      a := a + 1;
    }
  }
}

method Bitvectors1(A: bv3, B: bv3)
  requires A <= B
{
  var a, b := A, B;
  while a != b
    invariant a <= b
  {
    if * {
      b := b - 1;
    } else {
      a := a + 1;
    }
  }
}

method Chars0(A: char, B: char) {
  var a, b := A, B;
  while a < b {
    if * {
      b := b - 1 as char;
    } else {
      a := a + 1 as char;
    }
  }
}

method Chars1(A: char, B: char)
  requires A <= B
{
  var a, b := A, B;
  while a != b
    invariant a <= b
  {
    if * {
      b := b - 1 as char;
    } else {
      a := a + 1 as char;
    }
  }
}

method BigOrdinals0(B: ORDINAL)
{
  var b := B;
  while 0 < b
  {
    if b.IsLimit {
      var c :| c < b;
      b := c;
    } else {
      b := b - 1;
    }
  }
}

method BigOrdinals1(B: ORDINAL)
{
  var b := B;
  while b != 0
  {
    assert 0 < b;
    if b.IsLimit {
      var c :| c < b;
      b := c;
    } else {
      b := b - 1;
    }
  }
}

method BigOrdinals2(B: ORDINAL)
{
  var b, zero := B, 0;
  while b != zero // error: cannot prove termination (there's no auto-decreases guess)
  {
    assert 0 < b;
    if b.IsLimit {
      var c :| c < b;
      b := c;
    } else {
      b := b - 1;
    }
  }
}

method BigOrdinals3(A: ORDINAL, B: ORDINAL)
  requires A <= B
{
  var a, b := A, B;
  while a < b // error: this loop may go forever
  {
    a := a + 1;
  }
}

method BigOrdinals4(A: ORDINAL, B: ORDINAL) {
  var a, b := A, B;
  while a < b
  {
    if b.IsLimit {
      var c :| c < b;
      b := c;
    } else {
      b := b - 1;
    }
  }
}

// RUN: %verify --type-system-refresh=false --general-newtypes=false "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Here is the usual definition of possibly infinite lists, along with a function Tail(s, n), which drops
// n heads from s, and two lemmas that prove properties of Tail.

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

ghost function Tail(s: Stream, n: nat): Stream
{
  if n == 0 then s else
    var t := Tail(s, n-1);
    if t == Nil then t else t.tail
}

lemma Tail_Lemma0(s: Stream, n: nat)
  requires s.Cons? && Tail(s, n).Cons?
  ensures Tail(s, n).tail == Tail(s.tail, n)
{
}
lemma Tail_Lemma1(s: Stream, k: nat, n: nat)
  requires k <= n
  ensures Tail(s, n).Cons? ==> Tail(s, k).Cons?
  // Note, the contrapositive of this lemma says:  Tail(s, k) == Nil ==> Tail(s, n) == Nil
{
  if k < n && Tail(s, n).Cons? {
    assert Tail(s, n) == Tail(s, n-1).tail;
  }
}
lemma Tail_Lemma2(s: Stream, n: nat)
  requires s.Cons? && Tail(s.tail, n).Cons?
  ensures Tail(s, n).Cons?
{
  if n != 0 {
    Tail_Lemma0(s, n-1);
  }
}

// Co-predicate IsNeverEndingStream(s) answers whether or not s ever contains Nil.

greatest predicate IsNeverEndingStream<S>(s: Stream<S>)
{
  match s
  case Nil => false
  case Cons(_, tail) => IsNeverEndingStream(tail)
}

// Here is an example of an infinite stream.

ghost function AnInfiniteStream(): Stream<int>
{
  Cons(0, AnInfiniteStream())
}
greatest lemma Proposition0()
  ensures IsNeverEndingStream(AnInfiniteStream())
{
}

// Now, consider a Tree definition, where each node can have a possibly infinite number of children.

datatype Tree = Node(children: Stream<Tree>)

// Such a tree might have not just infinite width but also infinite height.  The following predicate
// holds if there is, for every path down from the root, a common bound on the height of each such path.
// Note that the definition needs a co-predicate in order to say something about all of a node's children.

ghost predicate HasBoundedHeight(t: Tree)
{
  exists n :: 0 <= n && LowerThan(t.children, n)
}
greatest predicate LowerThan(s: Stream<Tree>, n: nat)
{
  match s
  case Nil => true
  case Cons(t, tail) =>
    1 <= n && LowerThan(t.children, n-1) && LowerThan(tail, n)
}

// Co-predicate LowerThan(s, n) recurses on LowerThan(s.tail, n).  Thus, a property of LowerThan is that
// LowerThan(s, h) implies LowerThan(s', h) for any suffix s' of s.

lemma LowerThan_Lemma(s: Stream<Tree>, n: nat, h: nat)
  ensures LowerThan(s, h) ==> LowerThan(Tail(s, n), h)
{
  Tail_Lemma1(s, 0, n);
  if n == 0 || Tail(s, n) == Nil {
  } else {
    match s {
      case Cons(t, tail) =>
        LowerThan_Lemma(tail, n-1, h);
        Tail_Lemma0(s, n-1);
    }
  }
}

// A tree t where every node has an infinite number of children satisfies InfiniteEverywhere(t.children).
// Otherwise, IsFiniteSomewhere(t) holds.  That is, IsFiniteSomewhere says that the tree has some node
// with less than infinite width.  Such a tree may or may not be of finite height, as we'll see in an
// example below.

ghost predicate IsFiniteSomewhere(t: Tree)
{
  !InfiniteEverywhere(t.children)
}
greatest predicate InfiniteEverywhere(s: Stream<Tree>)
{
  match s
  case Nil => false
  case Cons(t, tail) => InfiniteEverywhere(t.children) && InfiniteEverywhere(tail)
}

// Here is a tree where every node has exactly 1 child.  Such a tree is finite in width (which implies
// it is finite somewhere) and infinite in height (which implies there is no bound on its height).

ghost function SkinnyTree(): Tree
{
  Node(Cons(SkinnyTree(), Nil))
}
lemma Proposition1()
  ensures IsFiniteSomewhere(SkinnyTree()) && !HasBoundedHeight(SkinnyTree())
{
  assert forall n {:induction} :: 0 <= n ==> !LowerThan(SkinnyTree().children, n);
}

// Any tree where all paths have bounded height are finite somewhere.

lemma Theorem0(t: Tree)
  requires HasBoundedHeight(t)
  ensures IsFiniteSomewhere(t)
{
  var n :| 0 <= n && LowerThan(t.children, n);
  /*
  assert (forall k :: 0 <= k ==> InfiniteEverywhere#[k](t.children)) ==> InfiniteEverywhere(t.children);
  assert InfiniteEverywhere(t.children) ==> (forall k :: 0 <= k ==> InfiniteEverywhere#[k](t.children));
  assert InfiniteEverywhere(t.children) <==> (forall k :: 0 <= k ==> InfiniteEverywhere#[k](t.children));  // TODO: why does this not follow from the previous two?
  */
  var k := FindNil(t.children, n);
}
lemma FindNil(s: Stream<Tree>, n: nat) returns (k: nat)
  requires LowerThan(s, n)
  ensures !InfiniteEverywhere#[k as ORDINAL](s)
{
  match s {
    case Nil => k := 1;
    case Cons(t, _) =>
	  k := FindNil(t.children, n-1);
	  k := k + 1;
  }
}

// We defined an InfiniteEverywhere property above and negated it to get an IsFiniteSomewhere predicate.
// If we had an InfiniteHeightSomewhere property, then we could negate it to obtain a predicate
// HasFiniteHeightEverywhere.  Consider the following definitions:

ghost predicate HasFiniteHeightEverywhere_Bad(t: Tree)
{
  !InfiniteHeightSomewhere_Bad(t.children)
}
greatest predicate InfiniteHeightSomewhere_Bad(s: Stream<Tree>)
{
  match s
  case Nil => false
  case Cons(t, tail) => InfiniteHeightSomewhere_Bad(t.children) || InfiniteHeightSomewhere_Bad(tail)
}

// In some ways, this definition may look reasonable--a list of trees is infinite somewhere
// if it is nonempty, and either the list of children of the first node satisfies the property
// or the tail of the list does.  However, because co-predicates are defined by greatest
// fix-points, there is nothing in this definition that "forces" the list to ever get to a
// node whose list of children satisfy the property.  The following example shows that a
// shallow, infinitely wide tree satisfies the negation of HasFiniteHeightEverywhere_Bad.

ghost function ATree(): Tree
{
  Node(ATreeChildren())
}
ghost function ATreeChildren(): Stream<Tree>
{
  Cons(Node(Nil), ATreeChildren())
}
lemma Proposition2()
  ensures !HasFiniteHeightEverywhere_Bad(ATree())
{
  Proposition2_Lemma0();
  Proposition2_Lemma1(ATreeChildren());
}
greatest lemma Proposition2_Lemma0()
  ensures IsNeverEndingStream(ATreeChildren())
{
}
greatest lemma Proposition2_Lemma1(s: Stream<Tree>)
  requires IsNeverEndingStream(s)
  ensures InfiniteHeightSomewhere_Bad(s)
{
  calc {
    InfiniteHeightSomewhere_Bad#[_k](s);
    InfiniteHeightSomewhere_Bad#[_k-1](s.head.children) || InfiniteHeightSomewhere_Bad#[_k-1](s.tail);
  <==
    InfiniteHeightSomewhere_Bad#[_k-1](s.tail);  // induction hypothesis
  }
}

// What was missing from the InfiniteHeightSomewhere_Bad definition was the existence of a child
// node that satisfies the property recursively.  To address that problem, we may consider
// a definition like the following:

/*
ghost predicate HasFiniteHeightEverywhere_Attempt(t: Tree)
{
  !InfiniteHeightSomewhere_Attempt(t.children)
}
greatest predicate InfiniteHeightSomewhere_Attempt(s: Stream<Tree>)
{
  exists n ::
    0 <= n &&
    var ch := Tail(s, n);
    ch.Cons? && InfiniteHeightSomewhere_Attempt(ch.head.children)
}
*/

// However, Dafny does not allow this definition:  the recursive call to InfiniteHeightSomewhere_Attempt
// sits inside an unbounded existential quantifier, which means the co-predicate's connection with its prefix
// predicate is not guaranteed to hold, so Dafny disallows this co-predicate definition.

// We will use a different way to express the HasFiniteHeightEverywhere property.  Instead of
// using an existential quantifier inside the recursively defined co-predicate, we can place a "larger"
// existential quantifier outside the call to the co-predicate.  This existential quantifier is going to be
// over the possible paths down the tree (it is "larger" in the sense that it selects a child tree at each
// level down the path, not just at one level).

// A path is a possibly infinite list of indices, each selecting the next child tree to navigate to.  A path
// is valid when it uses valid indices and does not stop at a node with children.

greatest predicate ValidPath(t: Tree, p: Stream<int>)
{
  match p
  case Nil => t == Node(Nil)
  case Cons(index, tail) =>
    0 <= index &&
    var ch := Tail(t.children, index);
    ch.Cons? && ValidPath(ch.head, tail)
}
lemma ValidPath_Lemma(p: Stream<int>)
  ensures ValidPath(Node(Nil), p) ==> p == Nil
{
  if ValidPath(Node(Nil), p) {
    match p {
      case Nil =>
      case Cons(index, tail) =>  // proof by contradiction
        var nil : Stream<Tree> := Nil;
        Tail_Lemma1(nil, 0, index);
    }
  }
}

// A tree has finite height (everywhere) if it has no valid infinite paths.

ghost predicate HasFiniteHeight(t: Tree)
{
  forall p :: ValidPath(t, p) ==> !IsNeverEndingStream(p)
}

// From this definition, we can prove that any tree of bounded height is also of finite height.

lemma Theorem1(t: Tree)
  requires HasBoundedHeight(t)
  ensures HasFiniteHeight(t)
{
  var n :| 0 <= n && LowerThan(t.children, n);
  forall p | ValidPath(t, p) {
    Theorem1_Lemma(t, n, p);
  }
}
lemma Theorem1_Lemma(t: Tree, n: nat, p: Stream<int>)
  requires LowerThan(t.children, n) && ValidPath(t, p)
  ensures !IsNeverEndingStream(p)
  decreases n
{
  match p {
    case Nil =>
    case Cons(index, tail) =>
      var ch := Tail(t.children, index);
      calc {
        LowerThan(t.children, n);
      ==>  { LowerThan_Lemma(t.children, index, n); }
        LowerThan(ch, n);
      ==>  // def. LowerThan
        LowerThan(ch.head.children, n-1);
      ==>  //{ Theorem1_Lemma(ch.head, n-1, tail); }
        !IsNeverEndingStream(tail);
      ==>  // def. IsNeverEndingStream
        !IsNeverEndingStream(p);
      }
  }
}

// In fact, HasBoundedHeight is strictly strong than HasFiniteHeight, as we'll show with an example.
// Define SkinnyFiniteTree(n) to be a skinny (that is, of width 1) tree of height n.

ghost function SkinnyFiniteTree(n: nat): Tree
  ensures forall k: nat :: LowerThan(SkinnyFiniteTree(n).children, k) <==> n <= k
{
  if n == 0 then Node(Nil) else Node(Cons(SkinnyFiniteTree(n-1), Nil))
}

// Next, we define a tree whose root has an infinite number of children, child i of which
// is a SkinnyFiniteTree(i).

ghost function FiniteUnboundedTree(): Tree
{
  Node(EverLongerSkinnyTrees(0))
}
ghost function EverLongerSkinnyTrees(n: nat): Stream<Tree>
{
  Cons(SkinnyFiniteTree(n), EverLongerSkinnyTrees(n+1))
}

lemma EverLongerSkinnyTrees_Lemma(k: nat, n: nat)
  ensures Tail(EverLongerSkinnyTrees(k), n).Cons?
  ensures Tail(EverLongerSkinnyTrees(k), n).head == SkinnyFiniteTree(k+n)
  decreases n
{
  if n == 0 {
  } else {
    calc {
      Tail(EverLongerSkinnyTrees(k), n);
      { EverLongerSkinnyTrees_Lemma(k, n-1); }  // this ensures that .tail on the next line is well-defined
      Tail(EverLongerSkinnyTrees(k), n-1).tail;
      { Tail_Lemma0(EverLongerSkinnyTrees(k), n-1); }
      Tail(EverLongerSkinnyTrees(k).tail, n-1);
      Tail(EverLongerSkinnyTrees(k+1), n-1);
    }
    EverLongerSkinnyTrees_Lemma(k+1, n-1);
  }
}

lemma Proposition3()
  ensures !HasBoundedHeight(FiniteUnboundedTree()) && HasFiniteHeight(FiniteUnboundedTree())
{
  Proposition3a();
  Proposition3b();
}
lemma Proposition3a()
  ensures !HasBoundedHeight(FiniteUnboundedTree())
{
  var ch := FiniteUnboundedTree().children;
  forall n | 0 <= n
    ensures !LowerThan(ch, n)
  {
    var cn := Tail(ch, n+1);
    EverLongerSkinnyTrees_Lemma(0, n+1);
    assert cn.head == SkinnyFiniteTree(n+1);
    assert !LowerThan(cn.head.children, n);
    LowerThan_Lemma(ch, n+1, n);
  }
}
lemma Proposition3b()
  ensures HasFiniteHeight(FiniteUnboundedTree())
{
  var t := FiniteUnboundedTree();
  forall p | ValidPath(t, p)
    ensures !IsNeverEndingStream(p)
  {
    assert p.Cons?;
    var index := p.head;
    assert 0 <= index;
    var ch := Tail(t.children, index);
    assert ch.Cons? && ValidPath(ch.head, p.tail);
    EverLongerSkinnyTrees_Lemma(0, index);
    assert ch.head == SkinnyFiniteTree(index);
    var si := SkinnyFiniteTree(index);
    assert LowerThan(si.children, index);
    Proposition3b_Lemma(si, index, p.tail);
  }
}
lemma Proposition3b_Lemma(t: Tree, h: nat, p: Stream<int>)
  requires LowerThan(t.children, h) && ValidPath(t, p)
  ensures !IsNeverEndingStream(p)
  decreases h
{
  match p {
    case Nil =>
    case Cons(index, tail) =>
      // From the definition of ValidPath(t, p), we get the following:
      var ch := Tail(t.children, index);
      // assert ch.Cons? && ValidPath(ch.head, tail);
      // From the definition of LowerThan(t.children, h), we get the following:
      match t.children {
        case Nil =>
          ValidPath_Lemma(p);
          assert false;  // absurd case
        case Cons(_, _) =>
          // assert 1 <= h;
          LowerThan_Lemma(t.children, index, h);
          // assert LowerThan(ch, h);
      }
      // Putting these together, by ch.Cons? and the definition of LowerThan(ch, h), we get:
      assert LowerThan(ch.head.children, h-1);
      // And now we can invoke the induction hypothesis:
      // Proposition3b_Lemma(ch.head, h-1, tail);
  }
}

// Using a stream of integers to denote a path is convenient, because it allows us to
// use Tail to quickly select the next child tree.  But we can also define paths in a
// way that more directly follows the navigation steps required to get to the next child,
// using Peano numbers instead of the built-in integers.  This means that each Succ
// constructor among the Peano numbers corresponds to moving "right" among the children
// of a tree node.  A path is valid only if it always selects a child from a list
// of children; this implies we must avoid infinite "right" moves.  The appropriate type
// Numbers (which is really just a stream of natural numbers) is defined as a combination
// two mutually recursive datatypes, one inductive and the other co-inductive.

codatatype CoOption<T> = None | Some(get: T)
datatype Number = Succ(Number) | Zero(CoOption<Number>)

// Note that the use of an inductive datatype for Number guarantees that sequences of successive
// "right" moves are finite (analogously, each Peano number is finite).  Yet the use of a co-inductive
// CoOption in between allows paths to go on forever.  In contrast, a definition like:

codatatype InfPath = Right(InfPath) | Down(InfPath) | Stop

// does not guarantee the absence of infinitely long sequences of "right" moves.  In other words,
// InfPath also gives rise to indecisive paths--those that never select a child node.  Also,
// compare the definition of Number with:

codatatype FinPath = Right(FinPath) | Down(FinPath) | Stop

// where the type can only represent finite paths.  As a final alternative to consider, had we
// wanted only infinite, decisive paths, we would just drop the None constructor, forcing each
// CoOption to be some Number.  As it is, we want to allow both finite and infinite paths, but we
// want to be able to distinguish them, so we define a co-predicate that does so:

greatest predicate InfinitePath(r: CoOption<Number>)
{
  match r
  case None => false
  case Some(num) => InfinitePath'(num)
}
greatest predicate InfinitePath'(num: Number)
{
  match num
  case Succ(next) => InfinitePath'(next)
  case Zero(r) => InfinitePath(r)
}

// As before, a path is valid for a tree when it navigates to existing nodes and does not stop
// in a node with more children.

greatest predicate ValidPath_Alt(t: Tree, r: CoOption<Number>)
{
  match r
  case None => t == Node(Nil)
  case Some(num) => ValidPath_Alt'(t.children, num)
}
greatest predicate ValidPath_Alt'(s: Stream<Tree>, num: Number)
{
  match num
  case Succ(next) => s.Cons? && ValidPath_Alt'(s.tail, next)
  case Zero(r) => s.Cons? && ValidPath_Alt(s.head, r)
}

// Here is the alternative definition of a tree that has finite height everywhere, using the
// new paths.

ghost predicate HasFiniteHeight_Alt(t: Tree)
{
  forall r :: ValidPath_Alt(t, r) ==> !InfinitePath(r)
}

// We will prove that this new definition is equivalent to the previous.  To do that, we
// first definite functions S2N and N2S to map between the path representations
// Stream<int> and CoOption<Number>, and then prove some lemmas about this correspondence.

ghost function S2N(p: Stream<int>): CoOption<Number>
  decreases 0
{
  match p
  case Nil => None
  case Cons(n, tail) => Some(S2N'(if n < 0 then 0 else n, tail))
}
ghost function S2N'(n: nat, tail: Stream<int>): Number
  decreases n + 1
{
  if n <= 0 then Zero(S2N(tail)) else Succ(S2N'(n-1, tail))
}

ghost function N2S(r: CoOption<Number>): Stream<int>
{
  match r
  case None => Nil
  case Some(num) => N2S'(0, num)
}
ghost function N2S'(n: nat, num: Number): Stream<int>
  decreases num
{
  match num
  case Zero(r) => Cons(n, N2S(r))
  case Succ(next) => N2S'(n + 1, next)
}

lemma Path_Lemma0(t: Tree, p: Stream<int>)
  requires ValidPath(t, p)
  ensures ValidPath_Alt(t, S2N(p))
{
  if ValidPath(t, p) {
    Path_Lemma0'(t, p);
  }
}
greatest lemma Path_Lemma0'(t: Tree, p: Stream<int>)
  requires ValidPath(t, p)
  ensures ValidPath_Alt(t, S2N(p))
{
  match p {
    case Nil =>
      assert t == Node(Nil);
    case Cons(index, tail) =>
      assert 0 <= index;
      var ch := Tail(t.children, index);
      assert ch.Cons? && ValidPath(ch.head, tail);

      calc {
        ValidPath_Alt#[_k](t, S2N(p));
        { assert S2N(p) == Some(S2N'(index, tail)); }
        ValidPath_Alt#[_k](t, Some(S2N'(index, tail)));
        // def. ValidPath_Alt#
        ValidPath_Alt'#[_k-1](t.children, S2N'(index, tail));
        { Path_Lemma0''(t.children, index, tail); }
        true;
      }
  }
}
greatest lemma Path_Lemma0''(tChildren: Stream<Tree>, n: nat, tail: Stream<int>)
  requires var ch := Tail(tChildren, n); ch.Cons? && ValidPath(ch.head, tail)
  ensures ValidPath_Alt'(tChildren, S2N'(n, tail))
{
  Tail_Lemma1(tChildren, 0, n);
  match S2N'(n, tail) {
    case Succ(next) =>
      calc {
        Tail(tChildren, n);
        { Tail_Lemma1(tChildren, n-1, n); }
        Tail(tChildren, n-1).tail;
        { Tail_Lemma0(tChildren, n-1); }
        Tail(tChildren.tail, n-1);
      }
      Path_Lemma0''(tChildren.tail, n-1, tail);
    case Zero(r) =>
      Path_Lemma0'(tChildren.head, tail);
  }
}
lemma Path_Lemma1(t: Tree, r: CoOption<Number>)
  requires ValidPath_Alt(t, r)
  ensures ValidPath(t, N2S(r))
{
  if ValidPath_Alt(t, r) {
    Path_Lemma1'(t, r);
  }
}
greatest lemma Path_Lemma1'(t: Tree, r: CoOption<Number>)
  requires ValidPath_Alt(t, r)
  ensures ValidPath(t, N2S(r))
  decreases 1
{
  match r {
    case None =>
      assert t == Node(Nil);
      assert N2S(r) == Nil;
    case Some(num) =>
      assert ValidPath_Alt'(t.children, num);
      // assert N2S'(0, num).Cons?;
      // Path_Lemma1''(t.children, 0, num);
      var p := N2S'(0, num);
      calc {
        ValidPath#[_k](t, N2S(r));
        ValidPath#[_k](t, N2S(Some(num)));
        ValidPath#[_k](t, N2S'(0, num));
        { Path_Lemma1''#[_k](t.children, 0, num); }
        true;
      }
  }
}
greatest lemma Path_Lemma1''(s: Stream<Tree>, n: nat, num: Number)
  requires ValidPath_Alt'(Tail(s, n), num)
  ensures ValidPath(Node(s), N2S'(n, num))
  decreases 0, num
{
  match num {
    case Succ(next) =>
      Path_Lemma1''#[_k](s, n+1, next);
    case Zero(r) =>
      calc {
        ValidPath#[_k](Node(s), N2S'(n, num));
        ValidPath#[_k](Node(s), Cons(n, N2S(r)));
        Tail(s, n).Cons? && ValidPath#[_k-1](Tail(s, n).head, N2S(r));
        { assert Tail(s, n).Cons?; }
        ValidPath#[_k-1](Tail(s, n).head, N2S(r));
        { Path_Lemma1'(Tail(s, n).head, r); }
        true;
      }
  }
}
lemma Path_Lemma2(p: Stream<int>)
  ensures IsNeverEndingStream(p) ==> InfinitePath(S2N(p))
{
  if IsNeverEndingStream(p) {
    Path_Lemma2'(p);
  }
}
greatest lemma Path_Lemma2'(p: Stream<int>)
  requires IsNeverEndingStream(p)
  ensures InfinitePath(S2N(p))
{
  match p {
  case Cons(n, tail) =>
    calc {
      InfinitePath#[_k](S2N(p));
      // def. S2N
      InfinitePath#[_k](Some(S2N'(if n < 0 then 0 else n, tail)));
      // def. InfinitePath
      InfinitePath'#[_k-1](S2N'(if n < 0 then 0 else n, tail));
    <== { Path_Lemma2''(p, if n < 0 then 0 else n, tail); }
      InfinitePath#[_k-1](S2N(tail));
      { Path_Lemma2'(tail); }
      true;
    }
  }
}
greatest lemma Path_Lemma2''(p: Stream<int>, n: nat, tail: Stream<int>)
  requires IsNeverEndingStream(p) && p.tail == tail
  ensures InfinitePath'(S2N'(n, tail))
{
  Path_Lemma2'(tail);
}
lemma Path_Lemma3(r: CoOption<Number>)
  ensures InfinitePath(r) ==> IsNeverEndingStream(N2S(r))
{
  if InfinitePath(r) {
    match r {
      case Some(num) => Path_Lemma3'(0, num);
    }
  }
}
greatest lemma Path_Lemma3'(n: nat, num: Number)
  requires InfinitePath'(num)
  ensures IsNeverEndingStream(N2S'(n, num))
  decreases num
{
  match num {
    case Zero(r) =>
      calc {
        IsNeverEndingStream#[_k](N2S'(n, num));
        // def. N2S'
        IsNeverEndingStream#[_k](Cons(n, N2S(r)));
        // def. IsNeverEndingStream
        IsNeverEndingStream#[_k-1](N2S(r));
        { Path_Lemma3'(0, r.get); }
        true;
      }
    case Succ(next) =>
      Path_Lemma3'#[_k](n + 1, next);
  }
}

lemma Theorem2(t: Tree)
  ensures HasFiniteHeight(t) <==> HasFiniteHeight_Alt(t)
{
  if HasFiniteHeight_Alt(t) {
    forall p {
      calc ==> {
        ValidPath(t, p);
        { Path_Lemma0(t, p); }
        ValidPath_Alt(t, S2N(p));
        // assumption HasFiniteHeight(t)
        !InfinitePath(S2N(p));
        { Path_Lemma2(p); }
        !IsNeverEndingStream(p);
      }
    }
  }
  if HasFiniteHeight(t) {
    forall r {
      calc ==> {
        ValidPath_Alt(t, r);
        { Path_Lemma1(t, r); }
        ValidPath(t, N2S(r));
        // assumption HasFiniteHeight_Alt(t)
        !IsNeverEndingStream(N2S(r));
        { Path_Lemma3(r); }
        !InfinitePath(r);
      }
    }
  }
}

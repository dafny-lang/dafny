// RUN: %exits-with 4 %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class UnboundedStack<T> {
  var top: Node?<T>
  ghost var footprint: set<object>
  ghost var content: seq<T>

  ghost predicate IsUnboundedStack()
    reads {this} + footprint
  {
    this in footprint &&
    (top == null  ==>  content == []) &&
    (top != null  ==>  top in footprint && top.footprint <= footprint &&
                       top.prev == null && content == top.content && top.Valid())
  }

  ghost predicate IsEmpty()
    reads {this};
  { content == [] }

  method Pop() returns (result: T)
    requires IsUnboundedStack() && !IsEmpty()
    modifies footprint
    ensures IsUnboundedStack() && content == old(content)[1..]
  {
    result := top.val;
    // The following assert does the trick, because it gets inlined and thus
    // exposes top.next.Valid() (if top.next != null):
    footprint := footprint - top.footprint;  top := top.next;
    // In a previous version of the implementation of the SplitExpr transformation, the
    // following assert did not have the intended effect of being used as a lemma:
    assert top != null ==> top.Valid();
    if top != null {
      footprint := footprint + top.footprint;  top.prev := null;
    }
    content := content[1..];
} }

class Node<T> {
  var val: T
  var next: Node?<T>
  var prev: Node?<T>
  var footprint: set<Node<T>>
  var content: seq<T>

  constructor (v: T) {
    val := v;
  }

  ghost predicate Valid()
    reads this, footprint
  {
    this in footprint &&
    (next == null  ==>  content == [val])  &&
    (next != null  ==>  next in footprint &&
                        next.footprint < footprint &&
                        !(this in next.footprint) &&
                        next.prev == this &&
                        content == [val] + next.content &&
                        next.Valid())
  }
}

// ---------------------------------------------------------------------------------------
// The following examples requires that quantifiers are boosted (that is, #2) when checked
// versus not boosted (#1) when assumed.

ghost function F(x: nat): int
{
  if x == 0 then 0 else 1 + F(x-1)
}

method M(N: nat)
{
  var i := 0;
  while i < N
    invariant forall x {:induction false} :: 0 <= x <= i ==> F(x) == x
  {
    i := i + 1;
  }
}

// ----- orderings of checked vs. free  -----
// The translation must always put checked things before free things.  In most situations,
// this does not actually matter, but it does matter for loop invariants of loops that have
// no backedges (that is, loops where Boogie's simple dead-code analysis figures prunes
// away the backedges.

ghost predicate AnyPredicate(a: int, b: int) { a <= b }

method NoLoop(N: nat)
{
  var i;
  while i < N
    invariant AnyPredicate(i, N)  // error: may not hold initially
  {
    i := i + 1;
    break;  // this makes the loop not a loop
  }
  assert AnyPredicate(i, N);
}

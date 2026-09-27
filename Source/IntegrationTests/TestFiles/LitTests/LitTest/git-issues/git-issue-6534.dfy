// RUN: %exits-with 4 %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The prelude had an axiom saying that every box is the box of a value of every type,
// which is false: at bool, every box would be $Box(true) or $Box(false). No program is
// known to prove false by it; the axioms themselves had no model (see the issue). The fix
// deletes it, and relies instead on the inverse for a box known to hold a value of the
// type. Proofs about fields had relied on the deleted axiom, so the fix also says that the
// value a field holds in the heap is a box of the field's type. Each constructor below
// needs that: its postcondition is about the box of the value just stored in a field.

class Node {
  var next: Node?
  constructor ()
  {
    next := null;
  }
}

class Queue {
  var head: Node
  ghost var spine: set<Node>

  constructor ()
    ensures head in spine
  {
    var n := new Node();
    head := n;
    spine := {n};
  }
}

class Booleans {
  var b: bool
  ghost var bs: set<bool>

  constructor (c: bool)
    ensures b in bs
  {
    b := c;
    bs := {c};
  }
}

// A vacuity control.  The facts the fix states are in play here: fields of several types are
// read and written, and their values go into collections as boxes.  With them present, false
// must still not be provable.
class Cell {
  var i: int
  var b: bool
  var next: Cell?
}

method Vacuity(c: Cell)
  modifies c
{
  c.i := c.i + 1;
  c.b := !c.b;
  var s: seq<int> := [c.i];
  var t: set<bool> := {c.b};
  var u: set<Cell?> := {c.next};
  assert s[0] == c.i && c.b in t && c.next in u;
  assert false; // error: must not be provable
}

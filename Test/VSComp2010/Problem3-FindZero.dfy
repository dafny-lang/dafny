// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// VSComp 2010, problem 3, find a 0 in a linked list and return how many nodes were skipped
// until the first 0 (or end-of-list) was found.
// Rustan Leino, 18 August 2010.
//
// The difficulty in this problem lies in specifying what the return value 'r' denotes and in
// proving that the program terminates.  Both of these are addressed by declaring a ghost
// field 'List' in each linked-list node, abstractly representing the linked-list elements
// from the node to the end of the linked list.  The specification can now talk about that
// sequence of elements and can use 'r' as an index into the sequence, and termination can
// be proved from the fact that all sequences in Dafny are finite.
//
// We only want to deal with linked lists whose 'List' field is properly filled in (which
// can only happen in an acyclic list, for example).  To that avail, the standard idiom in
// Dafny is to declare a predicate 'Valid()' that is true of an object when the data structure
// representing object's abstract value is properly formed.  The definition of 'Valid()'
// is what one intuitively would think of as the ''object invariant'', and it is mentioned
// explicitly in method pre- and postconditions.  As part of this standard idiom, one also
// declared a ghost variable 'Repr' that is maintained as the set of objects that make up
// the representation of the aggregate object--in this case, the Node itself and all its
// successors.

class Node {
  ghost var List: seq<int>
  ghost var Repr: set<Node>
  var head: int
  var next: Node?

  predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    1 <= |List| && List[0] == head &&
    (next == null ==> |List| == 1) &&
    (next != null ==>
      next in Repr && next.Repr <= Repr && this !in next.Repr && next.Valid() && next.List == List[1..])
  }

  static method Cons(x: int, tail: Node?) returns (n: Node)
    requires tail == null || tail.Valid()
    ensures n.Valid()
    ensures if tail == null then n.List == [x] else n.List == [x] + tail.List
  {
    n := new Node;
    n.head := x;
    n.next := tail;
    if (tail == null) {
      n.List := [x];
      n.Repr := {n};
    } else {
      n.List := [x] + tail.List;
      n.Repr := {n} + tail.Repr;
    }
  }
}

method Search(ll: Node?) returns (r: int)
  requires ll == null || ll.Valid()
  ensures ll == null ==> r == 0
  ensures ll != null ==>
            0 <= r && r <= |ll.List| &&
            (r < |ll.List| ==> ll.List[r] == 0 && 0 !in ll.List[..r]) &&
            (r == |ll.List| ==> 0 !in ll.List)
{
  if ll == null {
    r := 0;
  } else {
    var jj := ll;
    var i := 0;
    while jj != null && jj.head != 0
      invariant jj != null ==> jj.Valid() && i + |jj.List| == |ll.List| && ll.List[i..] == jj.List
      invariant jj == null ==> i == |ll.List|
      invariant 0 !in ll.List[..i]
      decreases |ll.List| - i
    {
      jj := jj.next;
      i := i + 1;
    }
    r := i;
  }
}

method Main()
{
  var list: Node? := null;
  list := Node.Cons(0, list);
  list := Node.Cons(5, list);
  list := Node.Cons(0, list);
  list := Node.Cons(8, list);
  var r := Search(list);
  print "Search returns ", r, "\n";
  assert r == 1;
}

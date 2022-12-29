// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=py "%s" "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

// This file contains several versions of a priority queue implemented by Braun trees:
//
//   PriorityQueue_extrinsic
//   +--PriorityQueue_layered
//   +--PriorityQueue_intrinsic
//      +--PriorityQueue_on_intrinsic
//   PriorityQueue_direct
//
// The specifications speak of the Elements of the priority queue, and the operations
// supported are Empty, Insert, and Min. (For brevity, Delete is omitted.)

module Client {
  import A = PriorityQueue_extrinsic
  import B = PriorityQueue_layered
  import C = PriorityQueue_intrinsic
  import D = PriorityQueue_on_intrinsic
  import E = PriorityQueue_direct

  method Main() {
    print "PriorityQueue_extrinsic: ", Test_extrinsic(), "\n";
    print "PriorityQueue_layered: ", Test_layered(), "\n";
    print "PriorityQueue_intrinsic: ", Test_intrinsic(), "\n";
    print "PriorityQueue_on_intrinsic: ", Test_on_intrinsic(), "\n";
    print "PriorityQueue_direct: ", Test_direct(), "\n";
  }

  function method Test_extrinsic(): int
    ensures Test_extrinsic() == 3
  {
    var p0 := A.Empty();
    var p1 := A.Insert(p0, 4);
    var p2 := A.Insert(p1, 3);
    A.AboutEmpty();
    A.AboutInsert(p0, 4);
    A.AboutInsert(p1, 3);
    assert A.Elements(p2) == multiset{3,4};
    A.AboutMin(p2);
    var m := A.Min(p2);
    m
  }

  function method Test_layered(): int
    ensures Test_layered() == 3
  {
    var p0 := B.Empty();
    var p1 := B.Insert(p0, 4);
    var p2 := B.Insert(p1, 3);
    assert B.Elements(p2) == multiset{3,4};
    var m := B.Min(p2);
    m
  }

  function method Test_intrinsic(): int
    ensures Test_intrinsic() == 3
  {
    var p0 := C.Empty();
    var p1 := C.Insert(p0, 4);
    var p2 := C.Insert(p1, 3);
    assert C.Elements(p2) == multiset{3,4};
    var m := C.Min(p2);
    m
  }

  function method Test_on_intrinsic(): int
    ensures Test_on_intrinsic() == 3
  {
    var p0 := D.Empty();
    var p1 := D.Insert(p0, 4);
    var p2 := D.Insert(p1, 3);
    assert D.Elements(p2) == multiset{3,4};
    var m := D.Min(p2);
    m
  }

  function method Test_direct(): int
    ensures Test_direct() == 3
  {
    var p0 := E.Empty();
    var p1 := E.Insert(p0, 4);
    var p2 := E.Insert(p1, 3);
    assert E.Elements(p2) == multiset{3,4};
    var m := E.Min(p2);
    m
  }
}

module PriorityQueue_layered {
  export
    provides T, Elements, Empty, Insert, Min
  import PQ = PriorityQueue_extrinsic
  type T = t: PQ.T | PQ.Valid(t) witness (PQ.AboutEmpty(); PQ.Empty())
  function Elements(t: T): multiset<int> {
    PQ.Elements(t)
  }
  function method Empty(): T
    ensures Elements(Empty()) == multiset{}
  {
    PQ.AboutEmpty();
    PQ.Empty()
  }
  function method Insert(t: T, x: int): T
    ensures Elements(Insert(t, x)) == Elements(t) + multiset{x}
  {
    PQ.AboutInsert(t, x);
    PQ.Insert(t, x)
  }
  function method Min(t: T): int
    requires Elements(t) != multiset{}
    ensures var m := Min(t);
      m in Elements(t) &&
      forall x :: x in Elements(t) ==> m <= x
  {
    PQ.AboutMin(t);
    PQ.Min(t)
  }
}

module PriorityQueue_on_intrinsic {
  export
    provides T, Elements, Empty, Insert, Min
  import PQ = PriorityQueue_intrinsic
  type T = t: PQ.T | PQ.Valid(t) witness PQ.Empty()
  function Elements(t: T): multiset<int> {
    PQ.Elements(t)
  }
  function method Empty(): T
    ensures Elements(Empty()) == multiset{}
  {
    PQ.Empty()
  }
  function method Insert(t: T, x: int): T
    ensures Elements(Insert(t, x)) == Elements(t) + multiset{x}
  {
    PQ.Insert(t, x)
  }
  function method Min(t: T): int
    requires Elements(t) != multiset{}
    ensures var m := Min(t);
      m in Elements(t) &&
      forall x :: x in Elements(t) ==> m <= x
  {
    PQ.Min(t)
  }
}

module PriorityQueue_intrinsic {
  export
    provides T, Valid, Elements, Empty, Insert, Min
  import PQ = PriorityQueue_extrinsic
  type T = PQ.T
  predicate Valid(t: T) {
    PQ.Valid(t)
  }
  function Elements(t: T): multiset<int> {
    PQ.Elements(t)
  }
  function method Empty(): T
    ensures var t' := Empty();
      Valid(t') && Elements(t') == multiset{}
  {
    PQ.AboutEmpty();
    PQ.Empty()
  }
  function method Insert(t: T, x: int): T
    requires Valid(t)
    ensures var t' := Insert(t, x);
      Valid(t') && Elements(t') == Elements(t) + multiset{x}
  {
    PQ.AboutInsert(t, x);
    PQ.Insert(t, x)
  }
  function method Min(t: T): int
    requires Valid(t) && Elements(t) != multiset{}
    ensures var m := Min(t);
      m in Elements(t) &&
      forall x :: x in Elements(t) ==> m <= x
  {
    PQ.AboutMin(t);
    PQ.Min(t)
  }
}

module PriorityQueue_extrinsic {
  export
    provides T, Valid, Elements, Empty, Insert, Min
    provides AboutEmpty, AboutInsert, AboutMin
  datatype T = Leaf | Node(val: int, left: T, right: T)
  predicate Valid(t: T)
  {
    match t
    case Leaf => true
    case Node(x, left, right) =>
      Valid(left) && Valid(right) &&
      (left == Leaf || x <= left.val) &&
      (right == Leaf || x <= right.val)
  }
  function Elements(t: T): multiset<int> {
    match t
    case Leaf => multiset{}
    case Node(x, left, right) => multiset{x} + Elements(left) + Elements(right)
  }
  function method Empty(): T
  {
    Leaf
  }
  lemma AboutEmpty()
    ensures var t' := Empty();
      Valid(t') && Elements(t') == multiset{}
  {
  }
  function method Insert(t: T, x: int): T
  {
    if t == Leaf then
      Node(x, Leaf, Leaf)
    else if x < t.val then
      Node(x, Insert(t.right, t.val), t.left)
    else
      Node(t.val, Insert(t.right, x), t.left)
  }
  lemma AboutInsert(t: T, x: int)
    requires Valid(t)
    ensures var t' := Insert(t, x);
      Valid(t') &&
      Elements(t') == Elements(t) + multiset{x}
  {
  }
  function method Min(t: T): int
    requires Elements(t) != multiset{}
  {
    t.val
  }
  lemma AboutMin(t: T)
    requires Valid(t) && Elements(t) != multiset{}
    ensures var m := Min(t);
      m in Elements(t) &&
      forall x :: x in Elements(t) ==> m <= x
  {
  }
}

module PriorityQueue_direct {
  export
    provides T, Elements, Empty, Insert, Min

  // Note that the left and right subtrees are also of type T' and
  // predicate Valid recurses on these subtrees. A plausible alternative
  // would be to define left and right to have type T and to omit the
  // recursive calls in Valid -- however, this gives rise to a cycle
  // T -> Valid -> T' -> T, which is not allowed.
  datatype T' = Leaf | Node(val: int, left: T', right: T')
  predicate Valid(t: T')
  {
    match t
    case Leaf => true
    case Node(x, left, right) =>
      Valid(left) && Valid(right) &&
      (left == Leaf || x <= left.val) &&
      (right == Leaf || x <= right.val)
  }
  type T = t: T' | Valid(t) witness Leaf

  function Elements(t: T): multiset<int> {
    match t
    case Leaf => multiset{}
    case Node(x, left, right) => multiset{x} + Elements(left) + Elements(right)
  }
  function method Empty(): T
    ensures Elements(Empty()) == multiset{}
  {
    Leaf
  }
  function method Insert(t: T, x: int): T
    ensures Elements(Insert(t, x)) == Elements(t) + multiset{x}
  {
    if t == Leaf then
      Node(x, Leaf, Leaf)
    else if x < t.val then
      Node(x, Insert(t.right, t.val), t.left)
    else
      Node(t.val, Insert(t.right, x), t.left)
  }
  function method Min(t: T): int
    requires Elements(t) != multiset{}
    ensures var m := Min(t);
      m in Elements(t) &&
      forall x :: x in Elements(t) ==> m <= x
  {
    AboutMin(t);
    t.val
  }
  lemma AboutMin(t: T)
    requires t != Leaf
    ensures t.val in Elements(t) &&
            forall x :: x in Elements(t) ==> t.val <= x
  {
    // this lemma is proved automatically by induction
  }
}

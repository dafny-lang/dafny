// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node<T> {
  var next: Node?<T>
}

class List<T> {
    ghost var spine: seq<Node<T>>
    ghost var repr: set<object>

    predicate Valid()
        reads this, repr
    {
        && forall i | 0 <= i < |spine| ::
            && spine[i] in repr
            && (spine[i].next == (if i < |spine| - 1 then spine[i+1] else null))
    }
}

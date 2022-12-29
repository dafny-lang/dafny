// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// ----------------------------------

predicate Trivial0(older x: int, s: set<int>) {
  true
}

predicate Trivial1(older x: int, s: set<int>) {
  x in s
}

predicate Trivial2(older x: int, s: set<int>) {
  x !in s
}

// ----------------------------------

predicate Trivial3<X(!new)>(older x: X, s: set<X>) {
  true
}

predicate Trivial4<X(!new)>(older x: X, s: set<X>) {
  x in s
}

predicate Trivial5<X(!new)>(older x: X, s: set<X>) {
  x !in s
}

// ----------------------------------

predicate Simple0<X>(older x: X, s: set<X>) { // error: x is not older
  true
}

predicate Simple1<X>(older x: X, s: set<X>) {
  x in s
}

predicate Simple2<X>(older x: X, s: set<X>) { // error: x is not older
  x !in s
}

// ----------------------------------

module Reachable0 {
  // This module shows how to get Reachable and ReachableVia to verify

  class Node {
    var children: seq<Node>
  }

  datatype Path<T> = Empty | Extend(Path, T)

  predicate Reachable(source: Node, sink: Node, S: set<Node>)
    reads S
  {
    exists via: Path<Node> :: ReachableVia(source, via, sink, S)
  }

  predicate ReachableVia(source: Node, older p: Path<Node>, sink: Node, S: set<Node>)
    reads S
    decreases p
  {
    match p
    case Empty => source == sink
    case Extend(prefix, n) => n in S && sink in n.children && ReachableVia(source, prefix, n, S)
  }
}

module Reachable1 {
  // This module packs more things into the Path, and there's no assurance that "p" in ReachableVia
  // is older than those things.

  class Node {
    var children: seq<Node>
  }

  datatype Path<T, Extra> = Empty | Extend(Path, T, Extra)

  predicate Reachable<Extra>(source: Node, sink: Node, S: set<Node>)
    reads S
  {
    exists via: Path<Node, Extra> :: ReachableVia(source, via, sink, S)
  }

  predicate ReachableVia<Extra>(source: Node, older p: Path<Node, Extra>, sink: Node, S: set<Node>) // error: cannot prove p is older
    reads S
    decreases p
  {
    match p
    case Empty => source == sink
    case Extend(prefix, n, extra) => n in S && sink in n.children && ReachableVia(source, prefix, n, S)
  }
}

module Reachable2 {
  // This module is like Reachable1, but the extra stuff is just integers.

  class Node {
    var children: seq<Node>
  }

  type Extra = int
  datatype Path<T, Extra> = Empty | Extend(Path, T, Extra)

  predicate Reachable(source: Node, sink: Node, S: set<Node>)
    reads S
  {
    exists via: Path<Node, Extra> :: ReachableVia(source, via, sink, S)
  }

  predicate ReachableVia(source: Node, older p: Path<Node, Extra>, sink: Node, S: set<Node>)
    reads S
    decreases p
  {
    match p
    case Empty => source == sink
    case Extend(prefix, n, extra) => n in S && sink in n.children && ReachableVia(source, prefix, n, S)
  }
}

module Reachable3 {
  // In this module, ReachableVia gives a "yes" answer for any path longer than a given limit. This
  // means it doesn't inspect all of "p" and hence one cannot conclude that "p" is indeed older.

  class Node {
    var children: seq<Node>
  }

  datatype Path<T> = Empty | Extend(Path, T)

  predicate Reachable(source: Node, sink: Node, S: set<Node>)
    reads S
  {
    exists via: Path<Node> :: ReachableVia(source, via, sink, S, 5)
  }

  predicate ReachableVia(source: Node, older p: Path<Node>, sink: Node, S: set<Node>, bound: nat) // error: cannot prove p is older
    reads S
    decreases p
  {
    bound != 0 ==>
    match p
    case Empty => source == sink
    case Extend(prefix, n) => n in S && sink in n.children && ReachableVia(source, prefix, n, S, bound - 1)
  }
}

module Reachable4 {
  // This module is like Reachable1, but ReachableVia always returns false. Therefore, p is indeed considered older.
  // To prove this requires a postcondition specification of ReachableVia.

  class Node {
    var children: seq<Node>
  }

  datatype Path<T, Extra> = Empty | Extend(Path, T, Extra)

  predicate Reachable<Extra>(source: Node, sink: Node, S: set<Node>)
    reads S
  {
    exists via: Path<Node, Extra> :: ReachableVia(source, via, sink, S)
  }

  predicate ReachableVia<Extra>(source: Node, older p: Path<Node, Extra>, sink: Node, S: set<Node>) // error: cannot prove p is older
    reads S
    decreases p
  {
    match p
    case Empty => false
    case Extend(prefix, n, extra) => n in S && sink in n.children && ReachableVia(source, prefix, n, S)
  }

  predicate ReachableViaEnsures<Extra>(source: Node, older p: Path<Node, Extra>, sink: Node, S: set<Node>)
    reads S
    ensures !ReachableViaEnsures(source, p, sink, S)
    decreases p
  {
    match p
    case Empty => false
    case Extend(prefix, n, extra) => n in S && sink in n.children && ReachableViaEnsures(source, prefix, n, S)
  }
}

module Reachable5 {
  // This module is like Reachable0, but uses two sets (S and T) instead of one (S)

  class Node {
    var children: seq<Node>
  }

  datatype Path<T> = Empty | Extend(Path, T)

  predicate Reachable(source: Node, sink: Node, S: set<Node>)
    reads S
  {
    exists via: Path<Node> :: ReachableVia(source, via, sink, S, S)
  }

  predicate ReachableVia(source: Node, older p: Path<Node>, sink: Node, S: set<Node>, T: set<Node>)
    reads S, T
    decreases p
  {
    match p
    case Empty => source == sink
    case Extend(prefix, n) => n in S && sink in n.children && ReachableVia(source, prefix, n, S, T)
  }
}

// ----------------------------------

module Comprehension {
  class C { }
  datatype List<T> = Nil | Cons(T, List<T>)

  predicate ElementsContainedIn<X>(older xs: List<X>, S: set<X>) {
    match xs
    case Nil => true
    case Cons(x, tail) => x in S && ElementsContainedIn(tail, S)
  }

  function Collection<X>(S: set<X>): iset<List<X>> {
    iset xs: List<X> | ElementsContainedIn(xs, S)
  }
}

// ----------------------------------

module MoreTests {
  class C { }
  datatype List<T> = Nil | Cons(T, List<T>)
  type Y = set<C>
  type X = List<C>

  predicate P(older x: X, y: Y) {
    match x
    case Nil => true
    case Cons(head, tail) => head in y && P(tail, y)
  }

  function F(y: Y): int {
    if forall x: X :: P(x, y) ==> G(x, y) == 3 then
      100
    else
      0
  }

  function G(x: X, y: Y): int

  function Collection(y: Y): iset<X> {
    iset x: X | P(x, y)
  }
}

// ----------------------------------

module VariationsOnPlurals {
  type X

  predicate One_None(older a: X) { // error: x is not older
    true
  }

  predicate One_One(older a: X, b: X) { // error: x is not older
    true
  }

  predicate One_Many(older a: X, b: X, c: X) { // error: x is not older
    true
  }

  predicate Many_None(older a: X, older b: X) { // error: x is not older
    true
  }

  predicate Many_One(older a: X, older b: X, c: X) { // error: x is not older
    true
  }

  predicate Many_Many(older a: X, older b: X, c: X, d: X) { // error: x is not older
    true
  }

  class C {
    predicate One_OneWithThis(older a: X) { // error: x is not older
      true
    }

    predicate One_ManyWithThis(older a: X, b: X) { // error: x is not older
      true
    }
  }
}

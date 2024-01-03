 // RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

module Basics {
  function F<A(!new)>(): int
  function G<A(0)>(): int
  function H<A(00)>(): int
  function J<A(==)>(): int

  type Cmp<A(==)>

  class Cell { }
  type Nonempty = x: int | x % 2 == 0 ghost witness 4
  datatype Record = Record(x: int, ghost y: int) // note, no equality support

  method Test()
    ensures F<Cell>() == 9 // error: type argument is required to support (!new)
    ensures G<Cell>() == 9 // error: type argument is required to support (0)
    ensures H<Cell>() == 9 // error: type argument is required to support (00)
    ensures J<Cell>() == 9
  {
    var x0 := F<Cell>(); // error: type argument is required to support (!new)
    var x1 := G<Nonempty>(); // error: type argument is required to support (0)
    var x2 := H<Nonempty>();
    var x3 := J<Record>(); // error: type argument is required to support (==)
    ghost var y0 := F<Cell>(); // error: type argument is required to support (!new)
    ghost var y1 := G<Nonempty>();
    ghost var y2 := H<Nonempty>();
    ghost var y3 := J<Record>();
  }

  method MethodSpecification(o: object)
    requires F<Cell>() < 100 // error: type argument is required to support (!new)
    modifies if F<Cell>() < 20 then {o} else {} // error: type argument is required to support (!new)
    ensures F<Cell>() < 100 // error: type argument is required to support (!new)
    decreases F<Cell>() // error: type argument is required to support (!new)

  function FunctionSpecification(o: object): int
    requires F<Cell>() < 100 // error: type argument is required to support (!new)
    reads if F<Cell>() < 20 then {o} else {} // error: type argument is required to support (!new)
    ensures F<Cell>() < 100 // error: type argument is required to support (!new)
    decreases F<Cell>() // error: type argument is required to support (!new)

  iterator IteratorSpecification(o: object)
    requires F<Cell>() < 100 // error: type argument is required to support (!new)
    yield requires F<Cell>() < 80 // error: type argument is required to support (!new)
    modifies if F<Cell>() < 20 then {o} else {} // error: type argument is required to support (!new)
    reads if F<Cell>() < 20 then {o} else {} // error: type argument is required to support (!new)
    yield ensures F<Cell>() < 80 // error: type argument is required to support (!new)
    ensures F<Cell>() < 100 // error: type argument is required to support (!new)
    decreases F<Cell>() // error: type argument is required to support (!new)

  method DefaultParameters0(x: int := J<Record>()) // error: type argument is required to support (==)
  method DefaultParameters1(ghost y: int := J<Record>())

  datatype DefaultValues =
    | Ctor0(x: int := J<Record>()) // error: type argument is required to support (==)
    | Ctor1(ghost y: int := J<Record>())
    | ghost Ctor2(z: int := J<Record>())

  function FunctionWithNamedResult(): (u: Cmp<Record>) // error: type argument is required to support (==)
  function FunctionWithUnnamedResult(): Cmp<Record> // error: type argument is required to support (==)
}

module Extreme {
  codatatype InfiniteTree<!A> = Node(value: int, next: A -> InfiniteTree)

  greatest predicate Bisimilar<A(!new)>(t: InfiniteTree, u: InfiniteTree) {
    && t.value == u.value
    && forall a: A :: Bisimilar(t.next(a), u.next(a))
  }

  greatest lemma SelfSimilar<A>(t: InfiniteTree<A>)
    ensures Bisimilar<A>(t, t) // error: type argument is required to support (!new)
  {
  }

  greatest lemma SelfSimilarCorrected<A(!new)>(t: InfiniteTree<A>)
    ensures Bisimilar<A>(t, t)
  {
  }

  class Class { }

  lemma SelfSimilarForClass(t: InfiniteTree<Class>)
    ensures Bisimilar<Class>(t, t) // error: type argument is required to support (!new)
  {
    SelfSimilarCorrected<Class>(t); // error: type argument is required to support (!new)
  }

  lemma SelfSimilarForClassHash(o: ORDINAL, t: InfiniteTree<Class>)
    ensures Bisimilar#<Class>[o](t, t) // error: type argument is required to support (!new)
  {
    SelfSimilarCorrected#<Class>[o](t); // error: type argument is required to support (!new)
  }
}

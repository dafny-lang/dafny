// RUN: %testDafnyForEachResolver "%s"


module ModifiesCallee {
  ghost function Wrap(S: set<object>): set<object> {
    S
  }

  method DoWrapped(S: set<object>)
    modifies Wrap(S)
  {
    DoOne(S);
  }

  method DoOne(S: set<object>)
    modifies S
  {
  }
}

module ModifiesCaller {
  ghost function Wrap(S: set<object>): set<object> {
    S
  }

  method DoWrapped(S: set<object>)
    modifies Wrap(S)
  {
  }

  method DoOne(S: set<object>)
    modifies S
  {
    DoWrapped(S);
  }
}

module ArraySeqInit {
  function F(a: int): int {
    45
  }

  method TestArrayF() {
    var m := new int[3](F);
    assert m[0] == 45;
  }

  method TestArrayLambda() {
    var m := new int[3](_ => 45);
    assert m[0] == 45;
  }

  method TestSeqF() {
    var m := seq(3, F);
    assert m[0] == 45;
  }

  method TestSeqLambda() {
    var m := seq(3, _ => 45);
    assert m[0] == 45;
  }

}

module QuantifierBeforeOtherConjunct {
  datatype List<T> = Nil | Cons(head: T, tail: List)

  function Length(list: List): nat {
    match list
    case Nil => 0
    case Cons(_, tl) => 1 + Length(tl)
  }

  function Occurrences(x: int, list: List<int>): nat
  {
    match list
    case Nil => 0
    case Cons(y, tl) => (if x == y then 1 else 0) + Occurrences(x, tl)
  }

  function Partition(x: int, l: List<int>): (result: (List<int>, List<int>))
    ensures
      && (forall y :: Occurrences(y, result.0) == if y <= x then Occurrences(y, l) else 0)
      && Length(l) == Length(result.0) + Length(result.1)

  lemma CallPartition(x: int, l: List<int>) returns (aaa: List<int>, bbb: List<int>)
    requires l.Cons? && l.head <= x
    ensures
      && (forall y :: Occurrences(y, aaa) == if y <= x then Occurrences(y, l) else 0)
      && Length(l) == Length(aaa) + Length(bbb)
  {
    var (lo, hi) := Partition(x, l.tail);
    aaa := Cons(l.head, lo);
    bbb := hi;
  }
}

// --------------------------------------------------

module TestInductiveDatatypes
{
  // The following types test for cycles that go via instantiated type arguments

  datatype Record<T> = Ctor(T);

  datatype RecInt = Ctor(Record<int>);  // this is fine
  datatype Rec_Forever = Ctor(Record<Rec_Forever>);  // error
  datatype Rec_Stops = Cons(Record<Rec_Stops>, Rec_Stops) | Nil;  // this is okay

  datatype D<T> = Ctor(E<D<T>>);  // error: illegal cycle
  datatype E<T> = Ctor(T);

  // the following is okay
  datatype MD<T> = Ctor(ME<T>);
  datatype ME<T> = Ctor(T);
  method M()
  {
    var d: MD<MD<int>>;
  }

  datatype A = Ctor(B);  // superficially looks like a cycle, but can still be constructed
  datatype B = Ctor(List<A>);
  datatype List<T> = Nil | Cons(T, List);
}

module MoreInductive {
  datatype Tree<G> = Node(G, List<Tree<G>>);
  datatype List<T> = Nil | Cons(T, List<T>);

  datatype M = All(List<M>);
  datatype H<'a> = HH('a, Tree<'a>);
  datatype K<'a> = KK('a, Tree<K<'a>>);  // error
  datatype L<'a> = LL('a, Tree<List<L<'a>>>);
}

// --------------------------------------------------

module TestCoinductiveDatatypes
{
  codatatype InfList<T> = Done | Continue(T, InfList);

  codatatype Stream<T> = More(T, Stream<T>);

  codatatype BinaryTreeForever<T> = BNode(val: T, left: BinaryTreeForever<T>, right: BinaryTreeForever<T>);

  datatype List<T> = Nil | Cons(T, List);

  codatatype BestBushEver<T> = Node(value: T, branches: List<BestBushEver<T>>);

  codatatype LazyRecord<T> = Lazy(contents: T);
  class MyClass<T> { }
  datatype GenericDt<T> = Blue | Green(T);
  datatype GenericRecord<T> = Rec(T);

  datatype FiniteEnough_Class = Ctor(MyClass<FiniteEnough_Class>);
  datatype FiniteEnough_Co = Ctor(LazyRecord<FiniteEnough_Co>);
  datatype FiniteEnough_Dt = Ctor(GenericDt<FiniteEnough_Dt>);  // fine
  datatype NotFiniteEnough_Dt = Ctor(GenericRecord<NotFiniteEnough_Dt>);  // error

}

// --------------- CoPredicates --------------------------

module CoPredicateResolutionErrors {

  codatatype Stream<T> = StreamCons(head: T, tail: Stream);

  function Upward(n: int): Stream<int>
  {
    StreamCons(n, Upward(n + 1))
  }

  function Doubles(n: int): Stream<int>
  {
    StreamCons(2*n, Doubles(n + 1))
  }

  copredicate Pos(s: Stream<int>)
  {
    0 < s.head && Pos(s.tail) && Even(s)
  }

  copredicate Even(s: Stream<int>)
  {
    s.head % 2 == 0 && Even(s.tail)
    && (s.head == 17 ==> Pos(s))
    && (Pos(s) ==> s.head == 17)  // error: cannot make recursive copredicate call in negative position
    && !Even(s)  // error: cannot make recursive copredicate call in negative position
    && (Even(s) <==> Even(s))  // error (x2): recursive copredicate calls allowed only in positive positions
  }

  copredicate Another(s: Stream<int>)
  {
    !Even(s)  // here, negation is fine
  }

  ghost method Lemma(n: int)
    ensures Even(Doubles(n));
  {
  }
}

// --------------------------------------------------

module InvalidCoMethodConclusions {
  codatatype Stream<T> = Cons(head: T, tail: Stream);

  copredicate Positive(s: Stream<int>)
  {
    s.head > 0 && Positive(s.tail)
  }

  comethod BadTheorem(s: Stream)
    ensures false;  // error: invalid comethod conclusion
  {
    BadTheorem(s.tail);
  }

  comethod CM(s: Stream<int>)
    ensures true && !false;
    ensures s.head == 8 ==> Positive(s);
    ensures s.tail == s;
    ensures s.head < 100;  // error: invalid comethod conclusion
    ensures Positive(s) ==> s.tail == s;
    ensures Positive(s) ==> s.head > 88;  // error: bad RHS of implication
    ensures !Positive(s) ==> s.tail == s;
    ensures !(true && !false ==> Positive(s) && !Positive(s));
    ensures !(false && !true ==> Positive(s) && !Positive(s));  // error: bad LHS of implication
  {
  }
}

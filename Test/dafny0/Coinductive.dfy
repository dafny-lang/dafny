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

// --------------------------------------------------

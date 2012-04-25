// The tests in this file are designed to run through the compiler.  They contain
// program snippets that are tricky to compile or whose compilation once was buggy.

datatype MyDt<T> = Nil | Cons(T, MyDt<T>);

method M<U>(x: MyDt<int>)
{
  match (x) {
    case Cons(head, tail) =>
      var y: int := head;
    case Nil =>
  }
}

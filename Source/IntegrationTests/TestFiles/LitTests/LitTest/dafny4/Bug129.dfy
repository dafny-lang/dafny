// RUN: %testDafnyForEachResolver "%s"


datatype Maybe<T> = Some(v:T) | None
datatype B = B(b:Maybe<B>)

datatype List<T> = Nil | Cons(T, List<T>)
datatype Tree<T> = Nodes(children: List<Tree<T>>)





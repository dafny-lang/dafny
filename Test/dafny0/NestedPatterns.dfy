// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method MethodA<T>(xs: List<T>) returns (ys: List<T>)
{
  match xs
  case Nil =>
    ys := Nil;
  case Cons(h, Nil) =>
    ys := Nil;
  case Cons(h, Cons(h', tt)) =>
    ys := tt;
}

method MethodB<T>(xs: List<T>)
{
  match xs
  case Nil =>
  case Cons(h, Nil) =>
    var x := 12;
    var xxs := Cons(Nil, Nil);
  case Cons(h, Cons(h', tt)) =>
}

method MethodC<T>(xs: List<T>) returns (ys: List<T>)
  requires xs.Cons? ==> !xs.tail.Cons?;
{
  match xs
  case Nil =>
    ys := Nil;
  case Cons(h, Nil) =>
    ys := Nil;
}

method MethodD<T>(xs: List<T>) returns (ys: List<T>)
{
  match xs
  case Nil =>
    ys := Nil;
  case Cons(h, Nil) =>
    var xxs: List<List<T>> := Cons(Nil, Nil);  // bug here is now fixed
  case Cons(h, Cons(h0, tt)) =>
}

method MethodE<T>(xs: List<T>) returns (ys: List<T>)
{
  var xxs: List<List<T>> := Cons(Nil, Nil);  // here it works! (but the same line in MethodD does not work)
}

method MethodF<T>(xs: List<T>) returns (ys: List<T>)
  requires xs.Cons? ==> !xs.tail.Cons?;
{
  match xs
  case Nil =>
  case Cons(h, Nil) =>
  case Cons(h0, Cons(h1, tt)) =>  // bug here is now fixed
}

method MethodG<T>(xs: List<T>) returns (xxs: List<List<T>>)
{
  match xs
  case Nil =>
    xxs := Cons(Nil, Nil);  // bugx here is now fixed
  case Cons(h, t) =>
  case Cons(h, Cons(ht, tt)) =>    // ERROR: redundant
}

method DuplicateIdentifierInPattern0<T>(xs: List<T>)
{
  match xs
  case Nil =>
  case Cons(h, Nil) =>
  case Cons(h, Cons(_, h)) =>  // ERROR: duplicate identifier
}

method DuplicateIdentifierInPattern1<T>(xs: List<T>)
{
  match xs
  case Nil =>
  case Cons(h, Nil) =>
  case Cons(h, Cons(h, _)) =>  // ERROR: duplicate identifier
}

method DuplicateIdentifierInPattern2<T>(xs: List<T>)
{
  match xs
  case Nil =>
  case Cons(h, Nil) =>
  case Cons(h, Cons(e, e)) =>  // ERROR: duplicate identifier
}

method Tuples0(xs: List, ys: List)
{
  match (xs, ys)
  case (Nil, Nil) =>
  case (Cons(a, b), Nil) =>
  case (Nil, Cons(x, y)) =>
  case (Cons(a, b), Cons(x, y)) =>  // BUG: here and in some other places above, not all identifiers are highlighted in the Dafny IDE; it looks like
                                    // only the identifiers in the last constructors are
}

method Tuples1(xs: List, ys: List)
{
  match (xs, ys, 4)
  case (Nil, Nil) =>  // ERROR: type mismatch (used to crash)

}

method Tuples2(xs: List, ys: List)
{
  match (xs, ys, ())
  case (Nil, Nil, ()) =>  // used to crash; now OK with unit matching
}

// RUN: %dafny /compile:0  "%s" > "%t"
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
    var xxs: List<List<T>> := Cons(Nil, Nil);  // BUG: type inference is not doing the right thing on this lint
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
  case Cons(h0, Cons(h1, tt)) =>  // BUG: Dafny complains that Cons appears in more than one case; it seems to be due to the
                                  // fact that the previous case uses identifier "h" as the first argument to Cons, whereas this
                                  // line uses "h0"
}

method MethodG<T>(xs: List<T>) returns (xxs: List<List<T>>)
{
  match xs
  case Nil =>
    xxs := Cons(Nil, Nil);  // BUG: this causes there to be an "unresolved identifier: _mc#0" error; oddly enough, the error goes away if the third case is commented out
  case Cons(h, t) =>
  case Cons(h, Cons(ht, tt)) => 
}

method AssertionFailure(xs: List)
{
  match xs
  case (Nil) =>  // BUG: this line causes an assertion in the Dafny implementation (what should happen is that "(Nil)" should not be allowed here)
  case (Cons(h, t)) =>  // BUG: ditto
}

method DuplicateIdentifierInPattern0<T>(xs: List<T>)
{
  match xs
  case Nil =>
  case Cons(h, Nil) =>
  case Cons(h, Cons(_, h)) =>  // BUG:  this duplicate identifier name should give rise to an error (from the Resolver), but no error is reported
}

method DuplicateIdentifierInPattern1<T>(xs: List<T>)
{
  match xs
  case Nil =>
  case Cons(h, Nil) =>
  case Cons(h, Cons(h, _)) =>  // BUG:  this duplicate identifier name should give rise to an error (from the Resolver), but no error is reported
}

method DuplicateIdentifierInPattern2<T>(xs: List<T>)
{
  match xs
  case Nil =>
  case Cons(h, Nil) =>
  case Cons(h, Cons(e, e)) =>  // BUG:  here, the duplicate identifier is detected, but the error message is shown 3 times, which is less than ideal
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
  case (Nil, Nil) =>  // BUG: the mismatch of 3 versus 2 arguments in the previous line and this line causes Dafny to crash with an
                      // assertion failure "mc.CasePatterns.Count == e.Arguments.Count"
}

method Tuples2(xs: List, ys: List)
{
  match (xs, ys, ())
  case (Nil, Nil, ()) =>  // BUG: Dafny crashes with an assertion failure "e.Arguments.Count >= 1"
}

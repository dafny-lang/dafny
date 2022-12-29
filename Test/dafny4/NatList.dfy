// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This file tests some programs where "nat" is a type parameter to
// a datatype.

datatype List<+T> = Nil | Cons(head: T, tail: List<T>)

method Main() {
  var ns := Nil;
  ns := Cons(4, Cons(10, Nil));
  print "ns = ", ns, "\n";
  print "Sum(ns) = ", Sum(ns), "\n";

  var ns' := Cons(20, Nil);
  var ns'' := Append(ns, ns');
  print "ns' = ", ns', "\n";
  print "Append(ns, ns') = ", ns'', "\n";
  print "Sum(Append(ns, ns')) = ", Sum(ns''), "\n";

  ConvertAndPrint(ns, -12);
}

function method Sum(ns: List<nat>): nat
{
  match ns
  case Nil => 0
  case Cons(n, tail) => n + Sum(tail)
}

function method Append<T>(xs: List<T>, ys: List<T>): List<T>
{
  match xs
  case Nil => ys
  case Cons(t, tail) => Cons(t, Append(tail, ys))
}

function method Negate(xs: List<int>): List<int>
{
  match xs
  case Nil => Nil
  case Cons(x, tail) => Cons(-x, Negate(tail))
}

lemma DoubleNegation(xs: List<int>)
  ensures Negate(Negate(xs)) == xs
{
  // proof by induction
}

method ConvertAndPrint(ns: List<nat>, nn: int)
  requires nn <= 0
{
  var xs := Negate(Negate(ns));
  DoubleNegation(ns);
  var ns': List<nat> := xs;
  print "Sum(Negate(Negate(ns))) = ", Sum(ns'), "\n";

  // In the following, no lemmas are needed, because "negs" is a literal so
  // functions applied to it will be fully expanded.
  var negs := Cons(-3, Cons(0, Cons(-2, Nil)));
  var s := Sum(Negate(negs));
  print "negs = ", negs, "\n";
  print "Sum(Negate(negs)) = ", s, "\n";

  // Here, the lemmas NatTan and Conversion_Int2Nat are needed.
  negs := Cons(-3, Cons(nn, Cons(-2, Nil)));
  assert ElementsAreTan(Cons(nn, Cons(-2, Nil)));  // help lemma
  NatTan(negs);
  var _ := Conversion_Int2Nat(Negate(negs));
  s := Sum(Negate(negs));
  print "negs = ", negs, "\n";
  print "Sum(Negate(negs)) = ", s, "\n";
}

lemma {:induction false} Conversion_Nat2Int(ns: List<nat>) returns (xs: List<int>)
  ensures ns == xs
{
  xs := ns;  // easy!
}

predicate ElementsAreNat(xs: List<int>)
{
  match xs
  case Nil => true
  case Cons(x, tail) => 0 <= x && ElementsAreNat(tail)
}

predicate ElementsAreTan(xs: List<int>)
{
  match xs
  case Nil => true
  case Cons(x, tail) => x <= 0 && ElementsAreTan(tail)
}

lemma NatTan(xs: List<int>)
  requires ElementsAreTan(xs)
  ensures ElementsAreNat(Negate(xs))
{
  // proof by induction
}

lemma {:induction false} Conversion_Int2Nat(xs: List<int>) returns (ns: List<nat>)
  requires ElementsAreNat(xs)
  ensures xs == ns
{
  match xs
  case Nil =>
    ns := xs;
  case Cons(x, tail) =>
    ns := Conversion_Int2Nat(tail);
    ns := Cons(x, ns);
}

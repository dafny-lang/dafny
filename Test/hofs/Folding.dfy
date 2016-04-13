// RUN: %dafny /compile:3 /autoTriggers:1 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Specifications and proofs involving foldr (inspired by Liquid Haskell) and foldl
// Rustan Leino
// 13 April 2016

method Main() {
  var xs := SeqToList([57, 100, -34, 1, 8]);
  var r := foldr((a,b) => 2*a + b, 0, xs);
  var l := foldl((b,a) => b + 2*a, 0, xs);
  print "xs = ", xs, "\n";
  print "foldr = ", r, "\n";
  print "foldl = ", l, "\n";
}

// ----- standard definitions ----------

datatype List<T> = Nil | Cons(T, List<T>)

function method SeqToList(s: seq): List
{
  if s == [] then Nil else Cons(s[0], SeqToList(s[1..]))
}

predicate Total2<T,U,R>(f: (T,U) -> R)
  reads f.reads
{
  forall t,u :: f.reads(t,u) == {} && f.requires(t,u)
}
predicate Total3<T,U,V,R>(f: (T,U,V) -> R)
  reads f.reads
{
  forall t,u,v :: f.reads(t,u,v) == {} && f.requires(t,u,v)
}

// ----- foldr ----------

function method foldr<A,B>(f: (A,B) -> B, b: B, xs: List<A>): B
  requires Total2(f)
{
  match xs
  case Nil => b
  case Cons(head, tail) => f(head, foldr(f, b, tail))
}

predicate Inv<A,B>(inv: (List<A>,B) -> bool, stp: (A,B,B) -> bool)
  requires Total2(inv) && Total3(stp)
{
  forall x, xs, b, b' ::
  inv(xs, b) && stp(x, b, b') ==> inv(Cons(x, xs), b')
}

lemma FoldR_Property<A,B>(inv: (List<A>,B) -> bool, stp: (A,B,B) -> bool, f: (A,B) -> B, b: B, xs: List<A>)
  requires Total2(inv) && Total3(stp) && Total2(f)
  requires Inv(inv, stp)
  requires forall a,b :: stp(a, b, f(a,b))
  requires inv(Nil, b)
  ensures inv(xs, foldr(f, b, xs))
{
  // Note:  Dafny is able to complete this whole proof automatically, so the following lines can all be erased.
  match xs
  case Nil =>
    // by the precondition
  case Cons(head, tail) =>
    var b' := foldr(f, b, tail);
    calc {
      true;
    ==>  // by the precondition that mentions "stp"
      stp(head, b', f(head, b'));
    ==>  // by the induction hypothesis invoked as FoldR_Property(inv, stp, f, b, tail)
      inv(tail, b') && stp(head, b', f(head, b'));
    ==>  // by Inv(inv, stp)
      inv(Cons(head, tail), f(head, b'));
    }
}

lemma FoldR_Use(xs: List<int>)
{
  var f := (a,b) => 2*a + 3*b;
  var r := foldr(f, 0, xs);
  ghost var inv := (xs,b) => b % 2 == 0;
  ghost var stp := (a,b,b') => b % 2 == 0 ==> b' % 2 == 0;
  FoldR_Property(inv, stp, f, 0, xs);
  assert r % 2 == 0;
}

// ----- foldl ----------

function method foldl<A,B>(f: (B,A) -> B, b: B, xs: List<A>): B
  requires Total2(f)
{
  match xs
  case Nil => b
  case Cons(head, tail) => foldl(f, f(b, head), tail)
}

predicate InvLeft<A,B>(inv: (B,List<A>) -> bool, stp: (B,A,B) -> bool)
  requires Total2(inv) && Total3(stp)
{
  forall x, xs, b, b' ::
  inv(b, Cons(x, xs)) && stp(b, x, b') ==> inv(b', xs)
}

lemma FoldL_Property<A,B>(inv: (B,List<A>) -> bool, stp: (B,A,B) -> bool, f: (B,A) -> B, b: B, xs: List<A>)
  requires Total2(inv) && Total3(stp) && Total2(f)
  requires InvLeft(inv, stp)
  requires forall b,a :: stp(b, a, f(b, a))
  requires inv(b, xs)
  ensures inv(foldl(f, b, xs), Nil)
{
  // Note:  In this case to complete the proof, Dafny needs the call to the induction hypothesis below, but
  // the rest of the calculation can be omitted.
  match xs
  case Nil =>
    // vacuous
  case Cons(head, tail) =>
    calc {
      true;
    ==>  // by the precondition
      inv(b, Cons(head, tail));
    ==>  // by the precondition that mentions "stp"
      inv(b, Cons(head, tail)) && stp(b, head, f(b, head));
    ==>  // by InvLeft(inv, stp)
      inv(f(b, head), tail);
    ==>  { FoldL_Property(inv, stp, f, f(b, head), tail); }  // induction hypothesis
      inv(foldl(f, f(b, head), tail), Nil);
    }
}

lemma FoldL_Use(xs: List<int>)
{
  var f := (b,a) => 3*b + 2*a;
  var l := foldl(f, 0, xs);
  ghost var inv := (b,xs) => b % 2 == 0;
  ghost var stp := (b,a,b') => b % 2 == 0 ==> b' % 2 == 0;
  FoldL_Property(inv, stp, f, 0, xs);
  assert l % 2 == 0;
}

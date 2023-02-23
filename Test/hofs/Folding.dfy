// RUN: %dafny /compile:3 /induction:3 "%s" > "%t"
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
  print "length = ", length(xs), "\n";
  print "foldr inc = ", foldr((_,b) => b+1, 0, xs), "\n";
  print "foldl inc = ", foldl((b,_) => b + 1, 0, xs), "\n";
}

// ----- standard definitions ----------

datatype List<T> = Nil | Cons(T, List<T>)

function method length(xs: List): nat
{
  match xs
  case Nil => 0
  case Cons(_, tail) => 1 + length(tail)
}

function method SeqToList(s: seq): List
{
  if s == [] then Nil else Cons(s[0], SeqToList(s[1..]))
}

// ----- foldr ----------

function method foldr<A,B>(f: (A,B) -> B, b: B, xs: List<A>): B
{
  match xs
  case Nil => b
  case Cons(head, tail) => f(head, foldr(f, b, tail))
}

// The following predicate says that "inv" is invariant under "stp".
// "stp" is really just a relational version of the function "f" passed to fold.
predicate InvR<A(!new),B(!new)>(inv: (List<A>,B) -> bool, stp: (A,B,B) -> bool)
{
  forall x, xs, b, b' ::
  inv(xs, b) && stp(x, b, b') ==> inv(Cons(x, xs), b')
}

lemma FoldR_Property<A,B>(inv: (List<A>,B) -> bool, stp: (A,B,B) -> bool, f: (A,B) -> B, b: B, xs: List<A>)
  requires InvR(inv, stp)
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
    ==>  // by InvR(inv, stp)
      inv(Cons(head, tail), f(head, b'));
    }
}

lemma FoldR_Property_ShortProof<A,B>(inv: (List<A>,B) -> bool, stp: (A,B,B) -> bool, f: (A,B) -> B, b: B, xs: List<A>)
  requires InvR(inv, stp)
  requires forall a,b :: stp(a, b, f(a,b))
  requires inv(Nil, b)
  ensures inv(xs, foldr(f, b, xs))
{
}

method FoldR_Use(xs: List<int>)
{
  var f := (a,b) => 2*a + 3*b;
  var r := foldr(f, 0, xs);
  ghost var inv := (xs,b) => b % 2 == 0;
  ghost var stp := (a,b,b') => b % 2 == 0 ==> b' % 2 == 0;
  FoldR_Property(inv, stp, f, 0, xs);
  assert r % 2 == 0;
}

// The (inv,stp) method of proof above is general, in the sense that it can be instantiated with (inv,stp).
// For a particular function, like F23, one can also prove a lemma about foldr directly.
function method F23(a: int, b: int): int {
  2*a + 3*b
}

lemma FoldR_F23(xs: List<int>)
  ensures foldr(F23, 0, xs) % 2 == 0
{
  // Note: With Z3 v.4.8.4, this proof had been automatic.
  // With Z3 v.4.8.9, the following empty match structure is needed.
  match xs
  case Nil =>
  case Cons(head, tail) =>
}

// In fact, it's also possible to write this lemma in an inline assertion.
method FoldR_Use_Direct(xs: List<int>)
{
  var r := foldr(F23, 0, xs);
  assert forall ys :: foldr(F23, 0, ys) % 2 == 0;
  assert r % 2 == 0;
}

method FoldR_Use_Direct_lambda(xs: List<int>)
{
  var f := (a,b) => 2*a + 3*b;
  var r := foldr(f, 0, xs);
  assert forall ys :: foldr(f, 0, ys) % 2 == 0;
  assert r % 2 == 0;
}

// It is not necessary to use the relation "stp".  Instead, the function "f" can be used directly.
lemma FoldR_Property_inv_f<A,B>(inv: (List<A>,B) -> bool, f: (A,B) -> B, b: B, xs: List<A>)
  requires forall x, xs, b :: inv(xs, b) ==> inv(Cons(x, xs), f(x, b))
  requires inv(Nil, b)
  ensures inv(xs, foldr(f, b, xs))
{
}

// Here's another use of the proof technique, showing that folding (+1) over a list gives its length.
lemma FoldingIncR(xs: List<int>)
  ensures foldr((_,b) => b + 1, 0, xs) == length(xs)
{
  FoldR_Property_inv_f((xs,b) => b == length(xs), (_,b) => b + 1, 0, xs);
}

// ----- foldl ----------

function method foldl<A,B>(f: (B,A) -> B, b: B, xs: List<A>): B
{
  match xs
  case Nil => b
  case Cons(head, tail) => foldl(f, f(b, head), tail)
}

// InvL is like InvR above, but the implication goes from larger lists to smaller ones (which is
// in the opposite direction from in InvR).
predicate InvL<A(!new),B(!new)>(inv: (B,List<A>) -> bool, stp: (B,A,B) -> bool)
{
  forall x, xs, b, b' ::
  inv(b, Cons(x, xs)) && stp(b, x, b') ==> inv(b', xs)
}

// This is the analogous lemma to FoldR_Property above.  But instead of proving
//     inv(Nil, b) ==> inv(xs, foldr(f, b, xs))
// this lemma proves
//     inv(b, xs) ==> inv(foldl(f, b, xs), Nil)
lemma FoldL_Property<A,B>(inv: (B,List<A>) -> bool, stp: (B,A,B) -> bool, f: (B,A) -> B, b: B, xs: List<A>)
  requires InvL(inv, stp)
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

// Here is FoldL_Property again, but this time with "f" instead of "stp".
lemma FoldL_Property_inv_f<A,B>(inv: (B,List<A>) -> bool, f: (B,A) -> B, b: B, xs: List<A>)
  requires forall x, xs, b :: inv(b, Cons(x, xs)) ==> inv(f(b, x), xs)
  requires inv(b, xs)
  ensures inv(foldl(f, b, xs), Nil)
{
  // the rest of the calculation can be omitted.
  match xs
  case Nil =>
  case Cons(head, tail) =>
    calc {
      true;
    ==>  // by the precondition
      inv(b, Cons(head, tail));
    ==>  // by the inductive property of "inv"
      inv(f(b, head), tail);
    ==>  { FoldL_Property_inv_f(inv, f, f(b, head), tail); }  // induction hypothesis
      inv(foldl(f, f(b, head), tail), Nil);
    }
}

// And as in the case of foldr, one can also use a specialized lemma for a particular function to be folded.
function method F32(b: int, a: int): int
{
  3*b + 2*a
}

lemma FoldL_F32(xs: List<int>, b: int)
  requires b % 2 == 0
  ensures foldl(F32, b, xs) % 2 == 0
{
}

method FoldL_Use_Direct(xs: List<int>)
{
  var r := foldl(F32, 0, xs);
  assert forall ys,b :: b % 2 == 0 ==> foldl(F32, b, ys) % 2 == 0;
  assert r % 2 == 0;
}

method {:vcs_split_on_every_assert} FoldL_Use_Direct_lambda(xs: List<int>)
{
  var f := (b,a) => 3*b + 2*a;
  var r := foldl(f, 0, xs);
  assert forall ys,b :: b % 2 == 0 ==> foldl(f, b, ys) % 2 == 0;
  assert r % 2 == 0;
}

// Here is a proof that foldl on (+1) gives the length.
lemma FoldingIncL(xs: List<int>)
  ensures foldl((b,_) => b + 1, 0, xs) == length(xs)
{
  var inv := (b,ys) => b + length(ys) == length(xs);
  var inc := (b,_) => b + 1;
  var r := foldl(inc, 0, xs);
  FoldL_Property_inv_f(inv, inc, 0, xs);
}

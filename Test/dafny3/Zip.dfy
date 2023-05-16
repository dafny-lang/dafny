// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*
Here, we define infinite streams with some functions and prove a few
properties, drawing from:

  Daniel Hausmann, Till Mossakowski and Lutz Schroder:
  Iterative Circular Coinduction for CoCasl in Isabelle/HOL.

Some proofs are automatic (EvenZipLemma), whereas some others require a single
recursive call to be made explicitly.

Note that the automatically inserted forall statement
is in principle strong enough in all cases above, but the incompletness
of reasoning with quantifiers in SMT solvers make the explicit calls
necessary.
*/

codatatype Stream<T> = Cons(hd: T, tl: Stream)

ghost function zip(xs: Stream, ys: Stream): Stream
  { Cons(xs.hd, Cons(ys.hd, zip(xs.tl, ys.tl))) }
ghost function even(xs: Stream): Stream
  { Cons(xs.hd, even(xs.tl.tl)) }
ghost function odd(xs: Stream): Stream
  { even(xs.tl) }

greatest lemma EvenOddLemma(xs: Stream)
  ensures zip(even(xs), odd(xs)) == xs;
{ EvenOddLemma(xs.tl.tl); }

greatest lemma EvenZipLemma(xs:Stream, ys:Stream)
  ensures even(zip(xs, ys)) == xs;
{ /* Automatic. */ }

ghost function bzip(xs: Stream, ys: Stream, f:bool) : Stream
  { if f then Cons(xs.hd, bzip(xs.tl, ys, !f))
    else      Cons(ys.hd, bzip(xs, ys.tl, !f)) }

greatest lemma BzipZipLemma(xs:Stream, ys:Stream)
  ensures zip(xs, ys) == bzip(xs, ys, true);
{ BzipZipLemma(xs.tl, ys.tl); }


/*
   More examples from CoCasl.
 */

ghost function constr(n:int): Stream<int>
{
  Cons(n, constr(n))
}

ghost function blink(): Stream<int>
{
  Cons(0, Cons(1, blink()))
}

greatest lemma BzipBlinkLemma()
  ensures zip(constr(0), constr(1)) == blink();
{
  BzipBlinkLemma();
}


ghost function zip2(xs: Stream, ys: Stream): Stream
{
  Cons(xs.hd, zip2(ys, xs.tl))
}

greatest lemma Zip201Lemma()
  ensures zip2(constr(0), constr(1)) == blink();
{
  Zip201Lemma();
}

greatest lemma ZipZip2Lemma(xs:Stream, ys:Stream)
  ensures zip(xs, ys) == zip2(xs, ys);
{
  ZipZip2Lemma(xs.tl, ys.tl);
}

ghost function bswitch(xs: Stream, f:bool) : Stream
{
  if f then Cons(xs.tl.hd, bswitch(Cons(xs.hd, xs.tl.tl), !f))
  else      Cons(xs.hd,      bswitch(xs.tl, !f))
}

greatest lemma BswitchLemma(xs:Stream)
  ensures zip(odd(xs), even(xs)) == bswitch(xs, true);
{
  BswitchLemma(xs.tl.tl);
}

greatest lemma Bswitch2Lemma(xs:Stream, ys:Stream)
  ensures zip(xs, ys) == bswitch(zip(ys, xs), true);
{
  Bswitch2Lemma(xs.tl, ys.tl);
}

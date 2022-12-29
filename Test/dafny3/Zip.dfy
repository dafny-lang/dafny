// RUN: %baredafny verify %args "%s" > "%t"
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

function zip(xs: Stream, ys: Stream): Stream
  { Cons(xs.hd, Cons(ys.hd, zip(xs.tl, ys.tl))) }
function even(xs: Stream): Stream
  { Cons(xs.hd, even(xs.tl.tl)) }
function odd(xs: Stream): Stream
  { even(xs.tl) }

greatest lemma EvenOddLemma(xs: Stream)
  ensures zip(even(xs), odd(xs)) == xs;
{ EvenOddLemma(xs.tl.tl); }

greatest lemma EvenZipLemma(xs:Stream, ys:Stream)
  ensures even(zip(xs, ys)) == xs;
{ /* Automatic. */ }

function bzip(xs: Stream, ys: Stream, f:bool) : Stream
  { if f then Cons(xs.hd, bzip(xs.tl, ys, !f))
    else      Cons(ys.hd, bzip(xs, ys.tl, !f)) }

greatest lemma BzipZipLemma(xs:Stream, ys:Stream)
  ensures zip(xs, ys) == bzip(xs, ys, true);
{ BzipZipLemma(xs.tl, ys.tl); }


/*
   More examples from CoCasl.
 */

function constr(n:int): Stream<int>
{
  Cons(n, constr(n))
}

function blink(): Stream<int>
{
  Cons(0, Cons(1, blink()))
}

greatest lemma BzipBlinkLemma()
  ensures zip(constr(0), constr(1)) == blink();
{
  BzipBlinkLemma();
}


function zip2(xs: Stream, ys: Stream): Stream
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

function bswitch(xs: Stream, f:bool) : Stream
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

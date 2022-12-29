// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A couple of examples from Grigore Rosu and Dorel Lucanu, "Circular coinduction: A proof theoretical
// foundation", CALCO 2009.

codatatype Stream<T> = Cons(head: T, tail: Stream)

// ----- standard examples -----

function zeros(): Stream<int> { Cons(0, zeros()) }
function ones(): Stream<int> { Cons(1, ones()) }
function blink(): Stream<int> { Cons(0, Cons(1, blink())) }
function zip(a: Stream, b: Stream): Stream { Cons(a.head, zip(b, a.tail)) }

greatest lemma BlinkZipProperty()
  ensures zip(zeros(), ones()) == blink();
{
    BlinkZipProperty();
}

// ----- Thue-Morse sequence -----

datatype Bit = O | I
function bitnot(b: Bit): Bit
{
  if b == O then I else O
}

function not(s: Stream<Bit>): Stream<Bit>
{
  Cons(bitnot(s.head), not(s.tail))
}

/* Function morse() is essentially this:

function morse(): Stream<int>
{
  Cons(0, morseTail())
}
function morseTail(): Stream<int>
{
  Cons(1, zip(morseTail(), not(morseTail())))
}

 * However, this definition of morseTail() is not allowed in Dafny, because it violates Dafny's
 * syntactic guardedness checks.  Instead, we give the defining properties of morse() and
 * morseTail() as an axiom (that is, an unproved lemma).
 */

function morse(): Stream<Bit>
function morseTail(): Stream<Bit>
lemma MorseProperties()
  ensures morse().head == O;
  ensures morseTail() == morse().tail;
  ensures morseTail().head == I;
  ensures morseTail().tail == zip(morseTail(), not(morseTail()));

// We will now define a function f and show that morse() is a fix-point of f.

function f(s: Stream<Bit>): Stream<Bit>
{
  Cons(s.head, Cons(bitnot(s.head), f(s.tail)))
}

// The insightful property about f is that it satisfies the following property, which
// we prove by co-induction.

greatest lemma FProperty(s: Stream<Bit>)
  ensures f(s) == zip(s, not(s));
{
  calc {
    zip(s, not(s));
    // def. zip
    Cons(s.head, zip(not(s), s.tail));
    // def. zip
    Cons(s.head, Cons(not(s).head, zip(s.tail, not(s).tail)));
  }
  FProperty(s.tail);
}

// The fix-point theorem now follows easily.

lemma Fixpoint()
  ensures f(morse()) == morse();
{
  MorseProperties();
  FProperty(morseTail());
}

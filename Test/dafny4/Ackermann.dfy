// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino, 8 Sep 2015.
// This file proves that the Ackermann function is monotonic in each argument

method Main() {
  // Note, don't try much larger numbers unless you're prepared to wait!
  print "Ack(3, 4) = ", Ack(3, 4), "\n";
}

// Here is the definition of the Ackermann function:
function method Ack(m: nat, n: nat): nat
{
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

// And here is the theorem that proves the desired result:
lemma AckermannIsMonotonic(m: nat, n: nat, m': nat, n': nat)
  requires m <= m' && n <= n'
  ensures Ack(m, n) <= Ack(m', n')
{
  // This is the proof.  It calls two lemmas, stated and proved below.
  MonotonicN(m, n, n');
  MonotonicM(m, n, m');
}

// --------------------------------------------------------
// What follows are the supporting lemmas and their proofs.
// --------------------------------------------------------

// Proving that Ackermann is monotonic in its second argument is easy.
lemma MonotonicN(m: nat, n: nat, n': nat)
  requires n <= n'
  ensures Ack(m, n) <= Ack(m, n')
{
  // In fact, Dafny completes this proof automatically.
}

// To prove the other direction, we consider an alternative formulation
// of the Ackermann function, namely a curried form:
function CurriedAckermann(m: int, n: int): int
{
  A(m)(n)
}

function A(m: int): int -> int
{
  if m <= 0 then
    n => n + 1
  else
    n => Iter(A(m-1), n)
}

function Iter(f: int -> int, n: int): int
  decreases n
{
  if n <= 0 then
    f(1)
  else
    f(Iter(f, n-1))
}

// Now, we can prove certain things about CurriedAckermann.  The first thing we
// prove is that it gives the same result as the Ack function above.

lemma CurriedIsTheSame(m: nat, n: nat)
  ensures CurriedAckermann(m, n) == Ack(m, n)
{
  // The proof considers 3 cases, following the 3 cases in the definition of Ack
  if m == 0 {
    // trivial
  } else if n == 0 {
      // Give Dafny some help unrolling these definitions
      // (note to advanced users: We need a bit more fuel
      //  to meet up with the induction hypothesis)
      assert CurriedAckermann(m, n) == Iter(A(m-1), 0);
  } else {
    // we help Dafny out with the following lemma:
    assert A(m)(n) == A(m-1)(Iter(A(m-1), n-1));
  }
}

// Monotonicity in the first argument of Ackermann now follows from the fact that,
// for m <= m', A(m) is a function that is always below A(m')
lemma MonotonicM(m: nat, n: nat, m': nat)
  requires m <= m'
  ensures Ack(m, n) <= Ack(m', n)
{
  CurriedIsTheSame(m, n);
  CurriedIsTheSame(m', n);
  ABelow(m, m');
}

// We must now prove ABelow.  To do that, we will prove some properties of A and of
// Iter.  Let us define the three properties we will reason about.

// The first property is a relation on functions.  It is the property that above was referred
// to as "f is a function that is always below g".  The lemma ABelow(m, m') used above establishes
// FunctionBelow(A(m), A(m')).
predicate FunctionBelow(f: int -> int, g: int -> int)
{
  forall n :: f(n) <= g(n)
}

// The next property says that a function is monotonic.
predicate FunctionMonotonic(f: int -> int)
{
  forall n,n' :: n <= n' ==> f(n) <= f(n')
}

// The third property says that a function's return value is strictly greater than its argument.
predicate Expanding(f: int -> int)
{
  forall n :: n < f(n)
}

// We will prove that A(_) satisfies the properties FunctionBelow, FunctionMonotonic, and
// FunctionExpanding.  But first we prove three properties of Iter.

// Provided that "f" is monotonic and expanding, Iter(f, _) is monotonic.
lemma IterIsMonotonicN(f: int -> int, n: int, n': int)
  requires Expanding(f) && FunctionMonotonic(f) && n <= n'
  ensures Iter(f, n) <= Iter(f, n')
{
  // This proof is a simple induction over n' and Dafny completes the proof automatically.
}

// Next, we prove that Iter(_, n) is monotonic.  That is, given functions "f" and "g"
// such that FunctionBelow(f, g), we have Iter(f, n) <= Iter(g, n).  The lemma requires
// "f" to be monotonic, but we don't have to state the same property for g.
lemma IterIsMonotonicF(f: int -> int, g: int -> int, n: int)
  requires FunctionMonotonic(f) && FunctionBelow(f, g)
  ensures Iter(f, n) <= Iter(g, n)
{
  // This proof is a simple induction over n and Dafny completes the proof automatically.
}

// Finally, we shows that for any expanding function "f", Iter(f, _) is also expanding.
lemma IterExpanding(f: int -> int, n: int)
  requires Expanding(f)
  ensures n < Iter(f, n)
{
  // Here, too, the proof is a simple induction of n and Dafny completes it automatically.
}

// We complete the proof by showing that A(_) has the three properties we need.

// Of the three properties we prove about A(_), we start by showing that A(m) returns a
// function that is expanding.
lemma AExp(m: int)
  ensures Expanding(A(m))
{
  if m <= 0 {
    // trivial
  } else {
    // This branch of the proof follows from the fact that Iter(A(m-1), _) is expanding.
    forall n {
      // The following lemma requires A(m-1) to be expanding, which is something that
      // following from our induction hypothesis.
      IterExpanding(A(m-1), n);
    }
  }
}

// Next, we show that A(m) returns a monotonic function.
lemma Am(m: int)
  ensures FunctionMonotonic(A(m))
{
  if m <= 0 {
    // trivial
  } else {
    // We make use of the fact that A(m-1) is expanding:
    AExp(m-1);
    // and the fact that Iter(A(m-1), _) is monotonic:
    forall n,n' | n <= n' {
      // The following lemma requires A(m-1) to be expanding and monotonic.
      // The former comes from the invocation of AExp(m-1) above, and the
      // latter comes from our induction hypothesis.
      IterIsMonotonicN(A(m-1), n, n');
    }
  }
}

// Our final property about A, which is the lemma we had used above to prove
// that Ackermann is monotonic in its first argument, is stated and proved here:
lemma ABelow(m: int, m': int)
  requires m <= m'
  ensures FunctionBelow(A(m), A(m'))
{
  if m' <= 0 {
    // trivial
  } else if m <= 0 {
    forall n {
      calc {
        A(m)(n);
      ==
        n + 1;
      <=  { AExp(m'-1); IterExpanding(A(m'-1), n); }
        Iter(A(m'-1), n);
      ==
        A(m')(n);
      }
    }
  } else {
    forall n {
      calc {
        A(m)(n);
      ==
        Iter(A(m-1), n);
      <=  { Am(m-1); ABelow(m-1, m'-1);
            IterIsMonotonicF(A(m-1), A(m'-1), n); }
        Iter(A(m'-1), n);
      ==
        A(m')(n);
      }
    }
  }
}

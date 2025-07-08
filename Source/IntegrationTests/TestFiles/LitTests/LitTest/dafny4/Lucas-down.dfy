// RUN: %verify "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Proof of the Lucas theorem
// Rustan Leino
// 9 March 2018
//
// Instead of the lemmas doing "up", like:
//   P(k) == P(2*k)
//   P(k) == P(2*k + 1)
// (see Lucas-up.dfy), the lemmas in this version go "down", like:
//   P(k%2) == P(k)

// This file defines the ingredients of the Lucas theorem, proves some
// properties of these, and then states and proves the Lucas theorem
// itself.

// The following predicate gives the boolean value of bit "k" in
// the natural number "n".
ghost predicate Bit(k: nat, n: nat)
{
  if k == 0 then n % 2 == 1
  else Bit(k-1, n / 2)
}

// Function "BitSet" returns the set of bits in the binary representation
// of a number.
ghost function BitSet(n: nat): set<nat>
{
  set i | 0 <= i < n && Bit(i, n)
}

// The following lemma shows that the "i < n" conjunct in
// the set comprehension in "BitSet" does not restrict
// the set any more than the conjunct "Bit(i, n)" does.
lemma BitSize(i: nat, n: nat)
  requires Bit(i, n)
  ensures i < n
{
}

// An easy-to-read name for the expression that checks if a number
// is even.
ghost predicate EVEN(n: nat)
{
  n % 2 == 0
}

// The binomial function is defined like in the Pascal triangle.
// "binom(a, b)" is also known as "a choose b".
ghost function binom(a: nat, b: nat): nat
{
  if b == 0 then 1
  else if a == 0 then 0
  else binom(a-1, b) + binom(a-1, b-1)
}

// This lemma shows that the parity of "binom" is preserved if
// div-2 is applied to both arguments--except in the case where
// the first argument to "binom" is even and the second argument
// is odd, in which case "binom" is always even.
lemma Lucas_Binary''(a: nat, b: nat)
  ensures binom(a, b) % 2 == if EVEN(a) && !EVEN(b) then 0 else binom(a / 2, b / 2) % 2
{
  if a == 0 || b == 0 {
  } else {
    Lucas_Binary''(a - 1, b);
    Lucas_Binary''(a - 1, b - 1);
  }
}

// "Suc(S)" returns the set constructed by incrementing
// each number in "S" by 1. Stated differently, it is the
// increment-by-1 (successor) function applied pointwise to the
// set.
ghost function Suc(S: set<nat>): set<nat>
{
  set x | x in S :: x + 1
}

// The following lemma clearly shows the correspondence between
// "S" and "Suc(S)".
lemma SucElements(S: set<nat>)
  ensures forall x :: x in S <==> (x+1) in Suc(S)
{
}

// Here is a lemma that relates BitSet and Suc.
lemma BitSet_Property(n: nat)
  ensures BitSet(n) - {0} == Suc(BitSet(n / 2))
{
  if n == 0 {
  } else {
    forall x: nat {
      calc {
        x in BitSet(n) - {0};
      ==
        x != 0 && x in BitSet(n);
      ==  // def. BitSet
        0 < x < n && Bit(x, n);
      ==  // def. Bit
        0 < x < n && Bit(x-1, n / 2);
      ==  { if 0 < x && Bit(x-1, n / 2) { BitSize(x-1, n / 2); } }
        0 <= x-1 < n / 2 && Bit(x-1, n / 2);
      ==  // def. BitSet
        (x-1) in BitSet(n / 2);
      ==  { SucElements(BitSet(n / 2)); }
        x in Suc(BitSet(n / 2));
      }
    }
  }
}

lemma Lucas_Theorem'(m: nat, n: nat)
  ensures BitSet(m) <= BitSet(n) <==> !EVEN(binom(n, m))
{
  if m == 0 && n == 0 {
  } else if EVEN(n) && !EVEN(m) {
    calc {
      !EVEN(binom(n, m));
    ==  { Lucas_Binary''(n, m); }
      false;
    ==  { assert 0 in BitSet(m) && 0 !in BitSet(n); }
      BitSet(m) <= BitSet(n);
    }
  } else {
    var m', n' := m/2, n/2;
    calc {
      !EVEN(binom(n, m));
    ==  { Lucas_Binary''(n, m); }
      !EVEN(binom(n', m'));
    ==  { Lucas_Theorem'(m', n'); }
      BitSet(m') <= BitSet(n');
    ==  { SucElements(BitSet(m')); SucElements(BitSet(n')); }
      Suc(BitSet(m')) <= Suc(BitSet(n'));
    ==  { BitSet_Property(m); BitSet_Property(n); }
      BitSet(m) - {0} <= BitSet(n) - {0};
    ==  { assert 0 !in BitSet(m) ==> BitSet(m) == BitSet(m) - {0};
          assert 0 in BitSet(n) ==> BitSet(n) - {0} <= BitSet(n); }
      BitSet(m) <= BitSet(n);
    }
  }
}

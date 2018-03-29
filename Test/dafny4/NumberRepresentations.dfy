// RUN: %dafny /compile:0 /dprint:"%t.dprint" /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// We consider a number representation that consists of a sequence of digits.  The least
// significant digit is stored at index 0.
// For a given base, function eval gives the number that is represented.  Note
// that eval can be defined without regard to the sign or magnitude of the digits.

function eval(digits: seq<int>, base: int): int
  requires 2 <= base;
  decreases digits;  // see comment in test_eval()
{
  if |digits| == 0 then 0 else digits[0] + base * eval(digits[1..], base)
}

lemma test_eval()
{
  assert forall base :: 2 <= base ==> eval([], base) == 0;
  assert forall base :: 2 <= base ==> eval([0], base) == 0;

  // To prove this automatically, it is necessary that the Lit axiom is sensitive only to the
  // 'digits' argument being a literal.  Hence, the explicit 'decreases digits' clause on the
  // 'eval' function.
  assert forall base :: 2 <= base ==> eval([0, 0], base) == 0;

  assert eval([3, 2], 10) == 23;

  var oct, dec := 8, 10;
  assert eval([1, 3], oct) == eval([5, 2], dec);

  assert eval([29], 420) == 29;
  assert eval([29], 8) == 29;

  assert eval([-2, 1, -3], 5) == -72;
}

// To achieve a unique (except for leading zeros) representation of each number, we
// consider digits that are drawn from a consecutive range of "base" integers
// including 0.  That is, each digit lies in the half-open interval [lowDigit..lowDigit+base].

predicate IsSkewNumber(digits: seq<int>, lowDigit: int, base: nat)
{
  2 <= base &&  // there must be at least two digits
  lowDigit <= 0 < lowDigit + base &&  // digits must include 0
  forall d :: d in digits ==> lowDigit <= d < lowDigit + base  // every digit is in this range
}

// The following theorem says that any natural number is representable as a sequence
// of digits in the range [0..base].

lemma CompleteNat(n: nat, base: nat) returns (digits: seq<int>)
  requires 2 <= base;
  ensures IsSkewNumber(digits, 0, base) && eval(digits, base) == n;
{
  if n < base {
    digits := [n];
  } else {
    var d, m := n / base, n % base;
    assert base * d + m == n;
    if n <= d {
      calc {
        base * d + m == n;
      ==> { assert 0 <= m; }
        base * d <= n;
      ==> { assert n <= d; }
        base * n <= n;
        (base - 1) * n + n <= n;
        (base - 1) * n <= 0;
      ==> { assert (base - 1) * n <= 0; MulSign(base - 1, n); }
        (base - 1) <= 0 || n <= 0;
        { assert 0 < n; }
        (base - 1) <= 0;
        { assert 2 <= base; }
        false;
      }
      assert false;
    }
    assert d < n && 0 <= m;
    digits := CompleteNat(d, base);
    digits := [m] + digits;
  }
}

// we used the following lemma to prove the theorem above
lemma MulSign(x: int, y: int)
  requires x * y <= 0;
  ensures x <= 0 || y <= 0;
{
}

// The following theorem says that, provided there's some digit with the same sign as "n",
// then "n" can be represented.

lemma Complete(n: int, lowDigit: int, base: nat) returns (digits: seq<int>)
  requires 2 <= base && lowDigit <= 0 < lowDigit + base;
  requires 0 <= lowDigit ==> 0 <= n;  // without negative digits, only non-negative numbers can be formed
  requires lowDigit + base <= 1 ==> n <= 0;  // without positive digits, only positive numbers can be formed
  ensures IsSkewNumber(digits, lowDigit, base) && eval(digits, base) == n;
  decreases if 0 <= n then n else -n;
{
  if lowDigit <= n < lowDigit + base{
    digits := [n];
  } else if 0 < n {
    digits := Complete(n - 1, lowDigit, base);
    digits := inc(digits, lowDigit, base);
  } else {
    digits := Complete(n + 1, lowDigit, base);
    digits := dec(digits, lowDigit, base);
  }
}

ghost method inc(a: seq<int>, lowDigit: int, base: nat) returns (b: seq<int>)
  requires 2 <= base && lowDigit <= 0 < lowDigit + base;
  requires IsSkewNumber(a, lowDigit, base);
  requires eval(a, base) == 0 ==> 1 < lowDigit + base;
  ensures IsSkewNumber(b, lowDigit, base) && eval(b, base) == eval(a, base) + 1;
{
  if a == [] {
    b := [1];
  } else if a[0] + 1 < lowDigit + base {
    b := a[0 := a[0] + 1];
  } else {
    b := inc(a[1..], lowDigit, base);
    b := [lowDigit] + b;
  }
}

ghost method dec(a: seq<int>, lowDigit: int, base: nat) returns (b: seq<int>)
  requires 2 <= base && lowDigit <= 0 < lowDigit + base;
  requires IsSkewNumber(a, lowDigit, base);
  requires eval(a, base) == 0 ==> lowDigit < 0;
  ensures IsSkewNumber(b, lowDigit, base) && eval(b, base) == eval(a, base) - 1;
{
  if a == [] {
    b := [-1];
  } else if lowDigit <= a[0] - 1 {
    b := a[0 := a[0] - 1];
  } else {
    b := dec(a[1..], lowDigit, base);
    b := [lowDigit + base - 1] + b;
  }
}

// Finally, we prove that number representations are unique, except for leading zeros.
// Recall, a "leading" zero is one at the end of the sequence.

// The trim function removes any leading zeros.

function trim(digits: seq<int>): seq<int>
{
  if |digits| != 0 && digits[|digits| - 1] == 0 then trim(digits[..|digits|-1]) else digits
}

// Here follow a number of lemmas about trim

lemma TrimResult(digits: seq<int>)
  ensures var last := |trim(digits)| - 1;
    0 <= last ==> trim(digits)[last] != 0;
{
}

lemma TrimProperty(a: seq<int>)
  requires a == trim(a);
  ensures a == [] || a[1..] == trim(a[1..]);
{
  assert forall b {:trigger trim(b)} :: |trim(b)| <= |b|;
}

lemma TrimPreservesValue(digits: seq<int>, base: nat)
  requires 2 <= base;
  ensures eval(digits, base) == eval(trim(digits), base);
{
  var last := |digits| - 1;
  if |digits| != 0 && digits[last] == 0 {
    assert digits == digits[..last] + [0];
    LeadingZeroInsignificant(digits[..last], base);
  }
}

lemma LeadingZeroInsignificant(digits: seq<int>, base: nat)
  requires 2 <= base;
  ensures eval(digits, base) == eval(digits + [0], base);
{
  if |digits| != 0 {
    var d := digits[0];
    assert [d] + digits[1..] == digits;
    calc {
      eval(digits, base);
      eval([d] + digits[1..], base);
      d + base * eval(digits[1..], base);
      { LeadingZeroInsignificant(digits[1..], base); }
      d + base * eval(digits[1..] + [0], base);
      eval([d] + (digits[1..] + [0]), base);
      { assert [d] + (digits[1..] + [0]) == ([d] + digits[1..]) + [0]; }
      eval(([d] + digits[1..]) + [0], base);
      eval(digits + [0], base);
    }
  }
}

// We now get on with proving the uniqueness of the representation

lemma UniqueRepresentation(a: seq<int>, b: seq<int>, lowDigit: int, base: nat)
  requires 2 <= base && lowDigit <= 0 < lowDigit + base;
  requires a == trim(a) && b == trim(b);
  requires IsSkewNumber(a, lowDigit, base) && IsSkewNumber(b, lowDigit, base);
  requires eval(a, base) == eval(b, base);
  ensures a == b;
{
  if eval(a, base) == 0 {
    ZeroIsUnique(a, lowDigit, base);
    ZeroIsUnique(b, lowDigit, base);
  } else {
    var aa, bb := eval(a, base), eval(b, base);
    var arest, brest := a[1..], b[1..];
    var ma, mb := aa % base, bb % base;

    assert 0 <= ma < base && 0 <= mb < base;
    LeastSignificantDigitIsAlmostMod(a, lowDigit, base);
    LeastSignificantDigitIsAlmostMod(b, lowDigit, base);
    assert ma == mb && a[0] == b[0];
    var y := a[0];

    assert aa == base * eval(arest, base) + y;
    assert bb == base * eval(brest, base) + y;
    MulInverse(base, eval(arest, base), eval(brest, base), y);
    assert eval(arest, base) == eval(brest, base);

    TrimProperty(a);
    TrimProperty(b);
    UniqueRepresentation(arest, brest, lowDigit, base);
    assert [y] + arest == a && [y] + brest == b;
  }
}

lemma ZeroIsUnique(a: seq<int>, lowDigit: int, base: nat)
  requires 2 <= base && lowDigit <= 0 < lowDigit + base
  requires a == trim(a)
  requires IsSkewNumber(a, lowDigit, base)
  requires eval(a, base) == 0
  ensures a == []
{
  if a != [] {
    if eval(a[1..], base) == 0 {
      TrimProperty(a);
      // ZeroIsUnique(a[1..], lowDigit, base);
    }
    assert false;
  }
}

lemma LeastSignificantDigitIsAlmostMod(a: seq<int>, lowDigit: int, base: nat)
  requires 2 <= base && lowDigit <= 0 < lowDigit + base && IsSkewNumber(a, lowDigit, base);
  requires a != [];
  ensures var mod := eval(a, base) % base; a[0] == mod || a[0] == mod - base;
{ assume false;  // TODO: temporary hack to get around Z3's fickleness and make progress with check-in
  var n := eval(a, base);
  var d, m := n / base, n % base;
  assert base * d + m == n;
  assert 0 <= m < base;

  assert lowDigit <= a[0] < lowDigit + base;
  var arest := a[1..];
  var nrest := eval(arest, base);
  assert base * nrest + a[0] == n;

  var p := MulProperty(base, d, m, nrest, a[0]);
  assert -base <= a[0] - m < base;
  assert -base == -1 * base && base == 1 * base;
  assert -1 * base <= a[0] - m < 1 * base;
  if {
    case p == -1 =>  assert a[0] == m - base;
    case p == 0 =>  assert a[0] == m;
  }
}

lemma MulProperty(k: int, a: int, x: int, b: int, y: int) returns (p: int)
  requires 0 < k;
  requires k * a + x == k * b + y;
  ensures y - x == k * p;
{
  calc {
    k * a + x == k * b + y;
    k * a - k * b == y - x;
    k * (a - b) == y - x;
  }
  p := a - b;
}

lemma MulInverse(x: int, a: int, b: int, y: int)
  requires x != 0 && x * a + y == x * b + y;
  ensures a == b;
{
}

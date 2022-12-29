// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// We consider a number representation that consists of a sequence of digits.  The least
// significant digit is stored at index 0.
// For a given base, function eval gives the number that is represented.  Note
// that eval can be defined without regard to the sign or magnitude of the digits.

function eval(digits: seq<int>, base: int): int
  requires 2 <= base
  decreases digits  // see comment in test_eval()
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

predicate IsSkewNumber(digits: seq<int>, lowDigit: int, base: int)
{
  2 <= base &&  // there must be at least two distinct digits in the number representation
  lowDigit <= 0 < lowDigit + base &&  // digits must include 0
  forall i :: 0 <= i < |digits| ==> lowDigit <= digits[i] < lowDigit + base  // every digit is in this range
}

// The following theorem says that any natural number is representable as a sequence
// of digits in the range [0..base].

lemma CompleteNat(n: nat, base: int) returns (digits: seq<int>)
  requires 2 <= base
  ensures IsSkewNumber(digits, 0, base) && eval(digits, base) == n
{
  if n < base {
    digits := [n];
  } else {
    var d, m := n / base, n % base;
    assert base * d + m == n;
    DivIsLess(n, base, d);
    assert d < n && 0 <= m;
    digits := CompleteNat(d, base);
    digits := [m] + digits;
  }
}

lemma DivIsLess(n: nat, base: int, d: int)
  requires 2 <= base <= n && d == n / base
  ensures d < n
{
  var m := n % base;
  if n <= d {
    calc {
      base * d + m == n;
    ==> { assert 0 <= m; }
      base * d <= n;
    ==> { assert n <= d; MulIsMonotonic(base, n, d); }
      base * n <= n;
      (base - 1) * n + n <= n;
      (base - 1) * n <= 0;
    ==> { assert (base - 1) * n <= 0; MulSign(base - 1, n); }
      (base - 1) <= 0 || n <= 0;
    ==  { assert 0 < n; }
      (base - 1) <= 0;
    ==  { assert 2 <= base; }
      false;
    }
    assert false;
  }
}

// we used the following lemma to prove the theorem above
lemma MulSign(x: int, y: int)
  requires x * y <= 0
  ensures x <= 0 || y <= 0
{
}

// The following theorem says that, provided there's some digit with the same sign as "n",
// then "n" can be represented.

lemma Complete(n: int, lowDigit: int, base: int) returns (digits: seq<int>)
  requires 2 <= base && lowDigit <= 0 < lowDigit + base
  requires 0 <= lowDigit ==> 0 <= n  // without negative digits, only non-negative numbers can be formed
  requires lowDigit + base <= 1 ==> n <= 0  // without positive digits, only positive numbers can be formed
  ensures IsSkewNumber(digits, lowDigit, base) && eval(digits, base) == n
  decreases if 0 <= n then n else -n
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

lemma inc(a: seq<int>, lowDigit: int, base: int) returns (b: seq<int>)
  requires IsSkewNumber(a, lowDigit, base)
  requires eval(a, base) == 0 ==> 1 < lowDigit + base
  ensures IsSkewNumber(b, lowDigit, base) && eval(b, base) == eval(a, base) + 1
{
  if a == [] {
    b := [1];
  } else if a[0] + 1 < lowDigit + base {
    b := a[0 := a[0] + 1];
  } else {
    // here's what we know about a:
    assert A: a[0] + 1 == lowDigit + base;
    var a' := a[1..];
    assert eval(a, base) == a[0] + base * eval(a', base);

    var b' := inc(a', lowDigit, base);
    assert eval(b', base) == eval(a', base) + 1;

    b := [lowDigit] + b';
    assert IsSkewNumber(b, lowDigit, base);

    calc {
      eval(b, base);
    ==  // def. eval
      b[0] + base * eval(b[1..], base);
    ==  { assert b[0] == lowDigit; }
      lowDigit + base * eval(b[1..], base);
    ==  { assert b[1..] == b'; }
      lowDigit + base * eval(b', base);
    ==  { assert eval(b', base) == eval(a', base) + 1; }
      lowDigit + base * (eval(a', base) + 1);
      lowDigit + base * eval(a', base) + base;
    ==  { reveal A; }
      a[0] + base * eval(a', base) + 1;
    ==  // def. eval
      eval(a, base) + 1;
    }
  }
}

lemma dec(a: seq<int>, lowDigit: int, base: int) returns (b: seq<int>)
  requires IsSkewNumber(a, lowDigit, base)
  requires eval(a, base) == 0 ==> lowDigit < 0
  ensures IsSkewNumber(b, lowDigit, base) && eval(b, base) == eval(a, base) - 1
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
    0 <= last ==> trim(digits)[last] != 0
{
}

lemma TrimProperty(a: seq<int>)
  requires a == trim(a)
  ensures a == [] || a[1..] == trim(a[1..])
{
  assert forall b {:induction} :: |trim(b)| <= |b|;
}

lemma TrimPreservesValue(digits: seq<int>, base: int)
  requires 2 <= base
  ensures eval(digits, base) == eval(trim(digits), base)
{
  var last := |digits| - 1;
  if |digits| != 0 && digits[last] == 0 {
    assert digits == digits[..last] + [0];
    LeadingZeroInsignificant(digits[..last], base);
  }
}

lemma LeadingZeroInsignificant(digits: seq<int>, base: int)
  requires 2 <= base
  ensures eval(digits, base) == eval(digits + [0], base)
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

lemma UniqueRepresentation(a: seq<int>, b: seq<int>, lowDigit: int, base: int)
  requires IsSkewNumber(a, lowDigit, base) && IsSkewNumber(b, lowDigit, base)
  requires a == trim(a) && b == trim(b)
  requires eval(a, base) == eval(b, base)
  ensures a == b
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

lemma {:induction false} ZeroIsUnique(a: seq<int>, lowDigit: int, base: int)
  requires IsSkewNumber(a, lowDigit, base)
  requires T: a == trim(a)
  requires E0: eval(a, base) == 0
  ensures a == []
{
  if a != [] {
    var a1 := eval(a[1..], base);
    var b := base * a1;
    assert a[0] + b == eval(a, base);

    assert R: -base < lowDigit <= a[0] < lowDigit + base <= base by {
      assert a[0] in a;
    }

    // next, consider three cases: a1 is negative, a1 is 0, a1 is positive

    calc {
      a1 <= -1;
    ==> { MulIsMonotonic(base, a1, -1); }  // multiply both sides by base
      base * a1 <= base * -1;
    ==>  { assert base * a1 == b; }
      b <= base * -1;
    ==  // add a[0] to both sides
      a[0] + b <= a[0] - base;
    ==  { reveal E0; }
      0 <= a[0] - base;
    ==
      base <= a[0];
    ==>  { reveal R; }
      false;
    }

    calc {
      1 <= a1;
    ==> { MulIsMonotonic(base, 1, a1); }  // multiply both sides by base
      base * 1 <= base * a1;
    ==  { assert base * 1 == base; }
      base <= base * a1;
    ==  // add a[0] to both sides
      a[0] + base <= a[0] + base * a1;
    ==  { reveal E0; }
      a[0] + base <= 0;
    ==
      a[0] <= -base;
    ==>  { reveal R; }
      false;
    }

    if a1 == 0 {
      assert |a| == 1 by {
        assert IsSkewNumber(a[1..], lowDigit, base) by {
          assert forall d :: d in a[1..] ==> d in a;
        }
        assert a[1..] == trim(a[1..]) by {
          reveal T;
          TrimProperty(a);
        }
        ZeroIsUnique(a[1..], lowDigit, base);
      }

      calc {
        true;
      ==
        a1 == 0;
      ==>  // multiply both sides by base
        base * a1 == 0;
      ==  // add a[0] to both sides
        a[0] + base * a1 == a[0];
      ==  { reveal E0; }
        0 == a[0];
      }

      calc {
        a;
      ==  { reveal T; }
        trim(a);
      ==  // def. trim
        if |a| != 0 && a[|a| - 1] == 0 then trim(a[..|a|-1]) else a;
      ==  { assert |a| == 1; }
        if a[0] == 0 then trim(a[..0]) else a;
      ==  { assert a[0] == 0; }
        trim(a[..0]);
      ==  { assert a[..0] == []; }
        trim([]);
      ==  // def. trim
        [];
      !=
        a;
      }
    }
  }
}

lemma LeastSignificantDigitIsAlmostMod(a: seq<int>, lowDigit: int, base: int)
  requires IsSkewNumber(a, lowDigit, base)
  requires a != []
  ensures var mod := eval(a, base) % base;
    a[0] == mod || a[0] == mod - base
{
  if 0 <= a[0] {
    LeastSignificantDigitIsAlmostMod_Pos(a, lowDigit, base);
  } else {
    LeastSignificantDigitIsAlmostMod_Neg(a, lowDigit, base);
  }
}

lemma LeastSignificantDigitIsAlmostMod_Pos(a: seq<int>, lowDigit: int, base: int)
  requires IsSkewNumber(a, lowDigit, base)
  requires a != [] && 0 <= a[0]
  ensures eval(a, base) % base == a[0]
{
  var n := eval(a, base);
  var a1 := eval(a[1..], base);
  var b := base * a1;
  assert a[0] + b == n;

  calc {
    n % base;
  ==
    (a[0] + base * a1) % base;
  ==  { ModProperty(a[0], a1, base); }
    a[0] % base;
  ==  { assert a[0] in a; ModNoop(a[0], base); }
    a[0];
  }
}

lemma LeastSignificantDigitIsAlmostMod_Neg(a: seq<int>, lowDigit: int, base: int)
  requires IsSkewNumber(a, lowDigit, base)
  requires a != [] && a[0] < 0
  ensures eval(a, base) % base == a[0] + base
{
  var n := eval(a, base);
  var a1 := eval(a[1..], base);
  var b := base * a1;
  assert a[0] + b == n;

  var aPlus, a1minus := a[0] + base, a1 - 1;
  calc {
    n % base;
  ==
    (a[0] + base * a1) % base;
  ==  { assert base * a1 == base + base * a1minus; }
    (a[0] + (base + base * a1minus)) % base;
  ==
    ((a[0] + base) + base * a1minus) % base;
  ==  { ModProperty(a[0] + base, a1minus, base); }
    (a[0] + base) % base;
  ==  { assert a[0] in a; ModNoop(a[0] + base, base); }
    a[0] + base;
  }
}


lemma ModProperty(n: int, k: int, base: int)
  requires 2 <= base
  ensures (n + base * k) % base == n % base
{
  var d, m := n / base, n % base;
  assert base * d + m == n;
  assert R: 0 <= m < base;

  var n' := n + base * k;
  var d', m' := n' / base, n' % base;
  assert base * d' + m' == n';
  assert R': 0 <= m' < base;

  assert -base < m' - m < base by {
    reveal R, R';
  }

  var y := m' - base * k;
  var p := MulProperty(base, d, m, d', y);
  var pk := p + k;
  calc {
    true;
    // postcondition of MulProperty
    y - m == base * p;
    // def. m'
    m' - base * k - m == base * p;
    // add base*k to both sides
    m' - m == base * p + base * k;
    // distribute * and +
    m' - m == base * pk;
  }
  if
  case pk < 0 =>
    MulIsMonotonic(base, pk, -1);
    assert base * pk <= -base;
    assert false;
  case 0 < pk =>
    MulIsMonotonic(base, 1, pk);
    assert base <= base * pk;
    assert false;
  case pk == 0 =>
    assert base * pk == 0;
    assert m' == m;
}

lemma MulIsMonotonic(a: int, x: int, y: int)
  requires 0 <= a && x <= y
  ensures a * x <= a * y
{
}

// This axiom about % is needed.  Unfortunately, Z3 v.4.8.9 seems incapable of proving it.
lemma ModNoop(a: int, b: int)
  requires 0 <= a < b
  ensures a % b == a

lemma MulProperty(k: int, a: int, x: int, b: int, y: int) returns (p: int)
  requires 0 < k
  requires k * a + x == k * b + y
  ensures y - x == k * p
{
  calc {
    k * a + x == k * b + y;
    k * a - k * b == y - x;
    k * (a - b) == y - x;
  }
  p := a - b;
}

lemma MulInverse(x: int, a: int, b: int, y: int)
  requires x != 0 && x * a + y == x * b + y
  ensures a == b
{
}

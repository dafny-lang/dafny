// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment --spill-translation

// A text describing this file is found in a Dafny Power User note: http://leino.science/papers/krml279.html

type pos = x | 1 <= x witness 1

ghost predicate IsFactor(p: pos, x: pos) {
  exists q :: p * q == x
}

lemma GetOtherFactor(p: pos, x: pos) returns (q: pos)
  requires IsFactor(p, x)
  ensures p * q == x
{
  q :| p * q == x;
}

ghost function Factors(x: pos): set<pos> {
  set p: pos | p <= x && IsFactor(p, x)
}

// The following lemma proves that the conjunct "p <= x" in the
// definition of Factors does not reduce the elements in the set.
lemma FactorIsInFactors(p: pos, x: pos)
  ensures p in Factors(x) <==> IsFactor (p, x)
{
}

lemma FactorsContains1(x: pos)
  ensures 1 in Factors(x)
{
  assert 1 * x == x;
}

lemma FactorsContainsSelf(x: pos)
  ensures x in Factors(x)
{
  assert x * 1 == x;
}

// This is a somewhat declarative definition of Max
ghost function Max(s: set<pos>): pos
  requires s != {}
{
  // To use the :| operator below, we need to prove that such a value exists
  MaxExists(s);
  var x :| x in s && forall y :: y in s ==> y <= x;
  x
}

lemma MaxExists(s: set<pos>)
  requires s != {}
  ensures exists x :: x in s && forall y :: y in s ==> y <= x
{
  // One way to show that such an x exists is to compute it
  var x := FindMax(s);
}

// Here is a recursive definition for computing the max
ghost function FindMax(s: set<pos>): (max: pos)
  requires s != {}
  ensures max in s && forall y :: y in s ==> y <= max
{
  var x :| x in s;
  if s == {x} then
    x
  else
    var s' := s - {x};
    assert s == s' + {x};
    var y := FindMax(s');
    if x < y then y else x
}

opaque ghost function Gcd(x: pos, y: pos): pos {
  var common := Factors(x) * Factors(y);
  assert 1 in common by {
    FactorsContains1(x);
    FactorsContains1(y);
  }
  Max(common)
}

lemma IsFactorGcdFirst(x: pos, y: pos)
  ensures IsFactor(Gcd(x, y), x)
{
  reveal Gcd();
}

lemma IsFactorGcdSecond(x: pos, y: pos)
  ensures IsFactor(Gcd(x, y), y)
{
  reveal Gcd();
}

lemma IsFactorGcdLess(x: pos, y: pos)
  ensures forall p: pos :: IsFactor(p, x) && IsFactor(p, y) ==> p <= Gcd(x, y)
{
  hide IsFactor;
  IsFactorGcdFirst(x, y);
  IsFactorGcdSecond(x, y);
  forall p: pos | IsFactor(p, x) && IsFactor(p, y)
    ensures p <= Gcd(x, y)
  {
    var qx := GetOtherFactor(p, x);
    var qy := GetOtherFactor(p, y);
    reveal Gcd();
    assert p in Factors(x) * Factors(y);
  }
}

lemma AboutGcd(x: pos, y: pos)
  ensures IsFactor(Gcd(x, y), x)
  ensures IsFactor(Gcd(x, y), y)
  ensures forall p: pos :: IsFactor(p, x) && IsFactor(p, y) ==> p <= Gcd(x, y)
{
  IsFactorGcdFirst(x, y);
  IsFactorGcdSecond(x, y);
  IsFactorGcdLess(x, y);
}

lemma GcdSymmetric(x: pos, y: pos)
  ensures Gcd(x, y) == Gcd(y, x)
{
  reveal Gcd();
  assert Factors(x) * Factors(y) == Factors(y) * Factors(x);
}

lemma GcdIdempotent(x: pos)
  ensures Gcd(x, x) == x
{
  FactorsContainsSelf(x);
  reveal Gcd();
  assert x in Factors(x) * Factors(x);
}

lemma {:isolate_assertions} GcdSubtract (x: pos, y: pos)
  requires x < y
  ensures Gcd(x, y) == Gcd(x, y - x)
{
  var p := Gcd(x, y);

  assert IsFactor (p, x) by {
    reveal Gcd();
    assert p in Factors(x);
    FactorIsInFactors(p, x);
  }

  assert IsFactor (p, y) by {
    reveal Gcd();
    assert p in Factors(y);
    FactorIsInFactors(p, y);
  }

  // By the definition of `Gcd`, we know that p is a factor of both x and y,
  // We now show that p is also a factor of y - x.
  assert IsFactor(p, y - x) by
  {
    var a :| p * a == x;
    var b :| p * b == y;
    calc {
      y - x;
    ==
      p * b - p * a;
    ==
      p * (b - a);
    }
  }

  // Hence, p is a common factor of x and y - x
  var common := Factors(x) * Factors(y - x);
  assert p in common;

  // It remains to show that, among the common factors of x and
  // y - x, p is the greatest
  forall q | q in common
    ensures q <= p
  {
    reveal Gcd();
    // q is a factor of both x and y - x, so a and b exist:
    var a :| q * a == x;
    var b :| q * b == y - x;
    assert IsFactor(q, y) by {
      calc {
        y;
      ==
        x + (y - x);
      ==
        q * a + q * b;
      ==
        q * (a + b);
      }
    }
    // We just showed that q is a common factor of x and y.
    assert q in Factors(x) * Factors(y);
    // By the definition of Gcd(x, y), we then have that q <= p.
  }
  assert Gcd(x, y) == Gcd(x, y - x) by {reveal Gcd();}
}

method EuclidGcd(X: pos, Y: pos) returns (gcd: pos)
  ensures gcd == Gcd(X, Y)
{
  var x: pos, y: pos := X, Y;
  while
    invariant Gcd(x, y) == Gcd(X, Y)
    decreases x + y
  {
    case x < y =>
      GcdSubtract(x, y);
      y := y - x;
    case y < x =>
      calc {
        Gcd(x, y);
      ==  { GcdSymmetric(x, y); }
        Gcd(y, x);
      ==  { GcdSubtract(y, x); }
        Gcd(y, x - y);
      ==  { GcdSymmetric(y, x - y); }
        Gcd(x - y, y);
      }
      x := x - y;
  }
  GcdIdempotent(x);
  return x;
}

// ------------------------------------------------------------------------------------------------------
// The alternative definitions that follow allow the two cases in the GCD algorithm to look more similar.

lemma {:isolate_assertions} GcdSubtractAlt(x: pos, y: pos)
  requires x < y
  ensures Gcd(y, x) == Gcd(x, y - x) // this says Gcd(y, x) instead of Gcd(x, y) as in GcdSubtract above
{
  GcdSymmetric(x, y); // this is the difference from GcdSubtract above
  var p := Gcd(x, y);

  assert IsFactor (p, x) by {
    reveal Gcd();
    assert p in Factors(x);
    FactorIsInFactors(p, x);
  }

  assert IsFactor (p, y) by {
    reveal Gcd();
    assert p in Factors(y);
    FactorIsInFactors(p, y);
  }

  assert IsFactor(p, y - x) by {
    var a :| p * a == x;
    var b :| p * b == y;
    assert y - x == p * (b - a) by {
      assert p * b - p * a == p * (b - a);
    }
  }

  var common := Factors(x) * Factors(y - x);
  assert p in common;

  forall q | q in common
    ensures q <= p
  {
    reveal Gcd();
    var a :| q * a == x;
    var b :| q * b == y - x;
    assert IsFactor(q, y)  by {
      calc {
        y;
      ==
        x + (y - x);
      ==
        q * a + q * b;
      ==
        q * (a + b);
      }
    }
    assert q in Factors(x) * Factors(y);
  }
  assert Gcd(y, x) == Gcd(x, y - x) by { reveal Gcd(); }
}

method EuclidGcdAlt(X: pos, Y: pos) returns (gcd: pos)
  ensures gcd == Gcd(X, Y)
{
  var x: pos, y: pos := X, Y;
  while
    invariant Gcd(x, y) == Gcd(X, Y)
    decreases x + y
  {
    case x < y =>
      GcdSubtractAlt(x, y);
      GcdSymmetric(y, x);
      y := y - x;
    case y < x =>
      GcdSymmetric(x - y, y);
      GcdSubtractAlt(y, x);
      x := x - y;
  }
  GcdIdempotent(x);
  return x;
}
// ------------------------------------------------------------------------------------------------------

method Main() {
  Test(15, 9);
  Test(14, 22);
  Test(371, 1);
  Test(1, 2);
  Test(1, 1);
  Test(13, 13);
  Test(60, 60);
}

method Test(x: pos, y: pos) {
  var gcd := EuclidGcd(x, y);
  print x, " gcd ", y, "  =  ", gcd, "\n";
}

// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This is a Dafny adaptation of a Coq program by David Pichardie.

ghost function IsEven(n: int): bool
  requires 0 <= n;
  ensures IsEven(n) ==> n == (n/2)+(n/2);
{
  (n/2)*2 == n
}

ghost function Square(n: int): int { n * n }

ghost function pow2(n: int): int
  requires 0 <= n;
  ensures 0 <= pow2(n);
{
  if n == 0 then
    1
  else if IsEven(n) then
    Square(pow2(n / 2))
  else
    2*pow2(n-1)

}

ghost function pow2_slow(n: int): int
  requires 0 <= n;
{
  if n == 0 then
    1
  else
    2*pow2_slow(n-1)
}

lemma Lemma(n: int)
  requires 0 <= n && IsEven(n);
  ensures pow2_slow(n) == Square(pow2_slow(n/2));
{
  if n != 0 {
    Lemma(n-2);
  }
}

lemma Theorem(n: int)
  requires 0 <= n;
  ensures pow2(n) == pow2_slow(n);
{
  if n == 0 {
  } else if (IsEven(n)) {
    Lemma(n);
    Theorem(n/2);
  } else {
    Theorem(n-1);
  }
}

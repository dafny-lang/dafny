// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype natinf = N(n: nat) | Inf

function S(x: natinf): natinf
{
  match x
  case N(n) => N(n+1)
  case Inf => Inf
}

inductive predicate Even(x: natinf)
{
  (x.N? && x.n == 0) ||
  (x.N? && 2 <= x.n && Even(N(x.n - 2)))
}

lemma M(x: natinf)
  requires Even(x)
  ensures x.N? && x.n % 2 == 0
{
  var k: nat :| Even#[k](x);
  M'(k, x);
}

// yay!  my first proof involving an inductive predicate :)
lemma M'(k: nat, x: natinf)
  requires Even#[k](x)
  ensures x.N? && x.n % 2 == 0
{
  if 0 < k {
    if {
      case x.N? && x.n == 0 =>
        // trivial
      case x.N? && 2 <= x.n && Even#[k-1](N(x.n - 2)) =>
        M'(k-1, N(x.n - 2));
    }
  }
}

lemma InfNotEven()
  ensures !Even(Inf)
{
}

lemma Test()
{
  assert !Even(N(1));  // Dafny can prove this
  assert !Even(N(5));
  assert !Even(N(17));  // error: this holds, but Dafny can't prove it directly (but see lemma below)
}

lemma SeventeenIsNotEven()
  ensures !Even(N(17))
{
  assert Even(N(17))
      == Even(N(15))
      == Even(N(13))
      == Even(N(11))
      == Even(N(9))
      == Even(N(7))
      == Even(N(5))
      == Even(N(3))
      == Even(N(1))
      == false;
}

lemma OneMore(x: natinf) returns (y: natinf)
  requires Even(x)
  ensures Even(y)
{
  y := N(x.n + 2);
}

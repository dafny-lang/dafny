// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype natinf = N(n: nat) | Inf

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

// Here is the same proof as in M / M', but packaged into a single "inductive lemma":
inductive lemma IL(x: natinf)
  requires Even(x)
  ensures x.N? && x.n % 2 == 0
{
  if {
    case x.N? && x.n == 0 =>
      // trivial
    case x.N? && 2 <= x.n && Even#[_k-1](N(x.n - 2)) =>
      IL(N(x.n - 2));
  }
}

inductive lemma IL_EvenBetter(x: natinf)
  requires Even(x)
  ensures x.N? && x.n % 2 == 0
{
  if {
    case x.N? && x.n == 0 =>
      // trivial
    case x.N? && 2 <= x.n && Even(N(x.n - 2)) =>
      IL_EvenBetter(N(x.n - 2));
  }
}

inductive lemma IL_Bad(x: natinf)
  requires Even(x)
  ensures x.N? && x.n % 2 == 0
{
  assert false;  // error: one shouldn't be able to prove just anything
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

// ----------------------- Here's another version of Even, using the S function

module Alt {
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
    exists y :: x == S(S(y)) && Even(y)
  }

  inductive lemma MyLemma_NotSoNice(x: natinf)
    requires Even(x)
    ensures x.N? && x.n % 2 == 0
  {
    if {
      case x.N? && x.n == 0 =>
        // trivial
      case exists y :: x == S(S(y)) && Even#[_k-1](y) =>
        var y :| x == S(S(y)) && Even#[_k-1](y);
        MyLemma_NotSoNice(y);
        assert x.n == y.n + 2;
    }
  }

  inductive lemma MyLemma_NiceButNotFast(x: natinf)
    requires Even(x)
    ensures x.N? && x.n % 2 == 0
  {
    if {
      case x.N? && x.n == 0 =>
        // trivial
      case exists y :: x == S(S(y)) && Even(y) =>
        var y :| x == S(S(y)) && Even(y);
        MyLemma_NiceButNotFast(y);
        assert x.n == y.n + 2;
    }
  }

  lemma InfNotEven()
    ensures !Even(Inf)
  {
    if Even(Inf) {
      InfNotEven_Aux();
    }
  }

  inductive lemma InfNotEven_Aux()
    requires Even(Inf)
    ensures false
  {
    var x := Inf;
    if {
      case x.N? && x.n == 0 =>
        assert false;  // this case is absurd
      case exists y :: x == S(S(y)) && Even(y) =>
        var y :| x == S(S(y)) && Even(y);
        assert y == Inf;
        InfNotEven_Aux();
    }
  }

  lemma NextEven(x: natinf)
    requires Even(x)
    ensures Even(S(S(x)))
  {
  }
}

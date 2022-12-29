// RUN: %exits-with 4 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

datatype natinf = N(n: nat) | Inf

least predicate Even(x: natinf)
{
  (x.N? && x.n == 0) ||
  (x.N? && 2 <= x.n && Even(N(x.n - 2)))
}

lemma M(x: natinf)
  requires Even(x)
  ensures x.N? && x.n % 2 == 0
{
  var k: ORDINAL :| Even#[k](x);
  M'(k, x);
}

// yay!  my first proof involving a least predicate :)
lemma {:induction false} M'(k: ORDINAL, x: natinf)
  requires Even#[k](x)
  ensures x.N? && x.n % 2 == 0
{
  if k.IsSucc {
    if {
      case x.N? && x.n == 0 =>
        // trivial
      case x.N? && 2 <= x.n && Even#[k-1](N(x.n - 2)) =>
        M'(k-1, N(x.n - 2));
    }
  } else {
    assert k.IsLimit;
    var k' :| k' < k && Even#[k'](x);
    M'(k', x);
  }
}

lemma M'_auto(k: ORDINAL, x: natinf)
  requires Even#[k](x)
  ensures x.N? && x.n % 2 == 0
{
}

// Here is the same proof as in M / M', but packaged into a single "least lemma":
least lemma {:induction false} IL(x: natinf)
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

least lemma {:induction false} IL_EvenBetter(x: natinf)
  requires Even(x)
  ensures x.N? && x.n % 2 == 0
{
  if {
    case x.N? && x.n == 0 =>
      // trivial
    case x.N? && 2 <= x.n && Even(N(x.n - 2)) =>  // syntactic rewrite makes this like in IL
      IL_EvenBetter(N(x.n - 2));
  }
}

least lemma IL_Best(x: natinf)
  requires Even(x)
  ensures x.N? && x.n % 2 == 0
{
}

least lemma IL_Bad(x: natinf)
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

  least predicate Even(x: natinf)
  {
    (x.N? && x.n == 0) ||
    exists y :: x == S(S(y)) && Even(y)
  }

  least lemma {:induction false} MyLemma_NotSoNice(x: natinf)
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

  least lemma {:induction false} MyLemma_Nicer(x: natinf)  // same as MyLemma_NotSoNice but relying on syntactic rewrites
    requires Even(x)
    ensures x.N? && x.n % 2 == 0
  {
    if {
      case x.N? && x.n == 0 =>
        // trivial
      case exists y :: x == S(S(y)) && Even(y) =>
        var y :| x == S(S(y)) && Even(y);
        MyLemma_Nicer(y);
        assert x.n == y.n + 2;
    }
  }

  least lemma MyLemma_RealNice_AndFastToo(x: natinf)
    requires Even(x)
    ensures x.N? && x.n % 2 == 0
  {
  }

  lemma InfNotEven()
    ensures !Even(Inf)
  {
    if Even(Inf) {
      InfNotEven_Aux();
    }
  }

  least lemma InfNotEven_Aux()
    requires Even(Inf)
    ensures false
  {
  }

  lemma NextEven(x: natinf)
    requires Even(x)
    ensures Even(S(S(x)))
  {
  }
}

/***********
 * These are test cases for monotonicity of the the _k parameter.  However, monotonicity
 * does not appear to be useful in the test suite, and it is possible that the axioms
 * about monotonicity are expensive performance-wise.  Therefore, the monotonicity axioms
 * are currently not produced--they are controled by #if WILLING_TO_TAKE_THE_PERFORMANCE_HIT.
 ***********
module Monotonicity {
  least predicate P(x: char)

  lemma MonotonicityP(k: ORDINAL, k': ORDINAL, x: char)
    requires P#[k](x) && k <= k'
    ensures P#[k'](x)
  {
  }

  least predicate Q[nat](x: char)

  lemma MonotonicityQ(k: nat, k': nat, x: char)
    requires Q#[k](x) && k <= k'
    ensures Q#[k'](x)
  {
  }

  greatest predicate H[nat](x: char)

  lemma MonotonicityH(k: nat, k': nat, x: char)
    requires H#[k](x) && k' <= k
    ensures H#[k'](x)
  {
  }

  greatest predicate J(x: char)

  lemma MonotonicityJ(k: ORDINAL, k': ORDINAL, x: char)
    requires J#[k](x) && k' <= k
    ensures J#[k'](x)
  {
  }
}
************/

// The following example is slightly tricky with ORDINALs, because of the limit
// step where one wants both P(x,y,z) and P(x,y,z') to go down to the same lower
// ORDINAL.  The targeted monotonicity axiom helps verify this example automatically.
module TargetedMonotonicity {
  function Next(x: int): int

  least predicate P(x: int, y: int, z: int)
  {
    (x == 0 && y == z) ||
    (x != 0 && P(Next(x), y, z))
  }

  least lemma Deterministic(x: int, y: int, z: int, z': int)
    requires P(x, y, z) && P(x, y, z')
    ensures z == z'
  {
    // take that!
  }
}

module SomeCoolDisjunctionTests {
  least predicate P[ORDINAL](x: int)
  {
    Q(x)
  }

  least predicate Q[ORDINAL](x: int)
  {
    P(x)
  }

  least lemma L[ORDINAL](x: int)
    requires P(x) || Q(x)
    ensures false  // fine
  {
  }

  least predicate Pn[nat](x: int)
  {
    Qn(x)
  }

  least predicate Qn[nat](x: int)
  {
    Pn(x)
  }

  least lemma Ln[nat](x: int)
    requires Pn(x) || Qn(x)
    ensures false  // fine
  {
  }
}

// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Rustan Leino, 22 Sep 2015.
// This file considers two definitions of Leq on naturals+infinity.  One
// definition uses the least fixpoint, the other the greatest fixpoint.

// Nat represents natural numbers extended with infinity
codatatype Nat = Z | S(pred: Nat)

function Num(n: nat): Nat
{
  if n == 0 then Z else S(Num(n-1))
}

predicate IsFinite(a: Nat)
{
  exists m:nat :: a == Num(m)
}

greatest predicate IsInfinity(a: Nat)
{
  a.S? && IsInfinity(a.pred)
}

lemma NatCases(a: Nat)
  ensures IsFinite(a) || IsInfinity(a)
{
  if IsFinite(a) {
  } else {
    NatCasesAux(a);
  }
}
greatest lemma NatCasesAux(a: Nat)
  requires !IsFinite(a)
  ensures IsInfinity(a)
{
  assert a != Num(0);
  if IsFinite(a.pred) {
    // going for a contradiction
    var m:nat :| a.pred == Num(m);
    assert a == Num(m+1);
    assert false;  // the case is absurd
  }
  NatCasesAux(a.pred);
}

// ----------- inductive semantics (more precisely, a least-fixpoint definition of Leq)

least predicate Leq(a: Nat, b: Nat)
{
  a == Z ||
  (a.S? && b.S? && Leq(a.pred, b.pred))
}

lemma LeqTheorem(a: Nat, b: Nat)
  ensures Leq(a, b) <==>
            exists m:nat :: a == Num(m) &&
                            (IsInfinity(b) || exists n:nat :: b == Num(n) && m <= n)
{
  if exists m:nat,n:nat :: a == Num(m) && b == Num(n) && m <= n {
    var m:nat,n:nat :| a == Num(m) && b == Num(n) && m <= n;
    Leq0_finite(m, n);
  }
  if (exists m:nat :: a == Num(m)) && IsInfinity(b) {
    var m:nat :| a == Num(m);
    Leq0_infinite(m, b);
  }
  if Leq(a, b) {
    var k :| Leq#[k](a, b);
    var m, n := Leq1(k, a, b);
  }
}

lemma Leq0_finite(m: nat, n: nat)
  requires m <= n
  ensures Leq(Num(m), Num(n))
{
  // proof is automatic
}

lemma Leq0_infinite(m: nat, b: Nat)
  requires IsInfinity(b)
  ensures Leq(Num(m), b)
{
  // proof is automatic
}

lemma Leq1(k: ORDINAL, a: Nat, b: Nat) returns (m: nat, n: nat)
  requires Leq#[k](a, b)
  ensures a == Num(m)
  ensures IsInfinity(b) || (b == Num(n) && m <= n)
{
  if k.IsLimit {
    var k' :| k' < k && Leq#[k'](a, b);
    m, n := Leq1(k', a, b);
  } else if a == Z {
    m := 0;
    NatCases(b);
    if !IsInfinity(b) {
      n :| b == Num(n);
    }
  } else {
    assert a.S? && b.S? && Leq(a.pred, b.pred);
    m,n := Leq1(k-1, a.pred, b.pred);
    m, n := m + 1, n + 1;
  }
}

// ----------- co-inductive semantics (more precisely, a greatest-fixpoint definition of Leq)

greatest predicate CoLeq(a: Nat, b: Nat)
{
  a == Z ||
  (a.S? && b.S? && CoLeq(a.pred, b.pred))
}

lemma CoLeqTheorem(a: Nat, b: Nat)
  ensures CoLeq(a, b) <==>
            IsInfinity(b) ||
            exists m:nat,n:nat :: a == Num(m) && b == Num(n) && m <= n
{
  if IsInfinity(b) {
    CoLeq0_infinite(a, b);
  }
  if exists m:nat,n:nat :: a == Num(m) && b == Num(n) && m <= n {
    var m:nat,n:nat :| a == Num(m) && b == Num(n) && m <= n;
    CoLeq0_finite(m, n);
  }
  if CoLeq(a, b) {
    CoLeq1(a, b);
  }
}

lemma CoLeq0_finite(m: nat, n: nat)
  requires m <= n
  ensures CoLeq(Num(m), Num(n))
{
  // proof is automatic
}

greatest lemma CoLeq0_infinite(a: Nat, b: Nat)
  requires IsInfinity(b)
  ensures CoLeq(a, b)
{
  // proof is automatic
}

lemma CoLeq1(a: Nat, b: Nat)
  requires CoLeq(a, b)
  ensures IsInfinity(b) || exists m:nat,n:nat :: a == Num(m) && b == Num(n) && m <= n
{
  var m,n := CoLeq1'(a, b);
}

lemma CoLeq1'(a: Nat, b: Nat) returns (m: nat, n: nat)
  requires CoLeq(a, b)
  ensures IsInfinity(b) || (a == Num(m) && b == Num(n) && m <= n)
{
  if !IsInfinity(b) {
    NatCases(b);
    n :| b == Num(n);
    m := CoLeq1Aux(a, n);
  }
}

lemma CoLeq1Aux(a: Nat, n: nat) returns (m: nat)
  requires CoLeq(a, Num(n))
  ensures a == Num(m) && m <= n
{
  if a == Z {
    m := 0;
  } else {
    m := CoLeq1Aux(a.pred, n-1);
    m := m + 1;
  }
}

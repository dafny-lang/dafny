// RUN: %verify --allow-warnings "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The matching-loop rewrite names n as int, whose translation is n, and c as Tr and old(F(x)), whose translations are
// those of another term of the trigger, so the trigger with the name's variable would not have the quantifier's own
// variable, or would have a term that is just the variable. Each translation leaves out such a trigger.

function F(x: int): int
function G(x: int, y: int): int
function K(x: int): int

method Assumption() {
  assume {:axiom} forall n: int :: F(n) <= F(n as int);
}

trait Tr { }
class Cl extends Tr { }
predicate P(t: Tr)

lemma Upcast(d: Cl)
  requires forall c: Cl :: P(c) ==> P(c as Tr)
  ensures P(d) ==> P(d as Tr)
{
}

method Old() {
  assume {:axiom} forall x :: K(x) <= K(old(F(x)));
}

ghost function CanCall(): bool {
  forall n: nat :: F(n) <= F(n as int)
}

method SuchThat() {
  assume {:axiom} F(3) <= F(3);
  var x: nat :| F(x) <= F(x as int);
}

ghost function LetSuchThat(): nat
  requires exists n: nat :: F(n) <= F(n as int)
{
  var n: nat :| F(n) <= F(n as int); n
}

lemma L(n: nat)
  ensures F(n) <= F(n as int)
{
}

method ForallStatement() {
  forall n: nat | n < 10 {
    L(n);
  }
}

lemma {:induction n} Induction(n: nat)
  ensures forall m: nat :: G(m, n) <= G(m as int, n)
{
  assume {:axiom} false;
}

function H(b: bool): int

// The assumption of a forall assignment's new values does not bind named terms, as !b here, so it has no triggers
// with them
method Assignment(a: array<int>)
  modifies a
{
  forall b: bool {:split false} | 0 <= H(b) < a.Length && 0 <= H(!b) < a.Length {
    a[H(b)] := H(!b);
  }
}

// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /autoTriggers:1 /printTooltips "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

lemma Tests<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures !z
{
  if {
    case true =>
      z := 72 in set i | 0 <= i < 10;
    case true =>
      z := -8 in set k: nat | k < 10;
    case true =>
      z := 6 in set m | 0 <= m < 10 && Even(m) :: m + 1;
    case true =>
      z := t !in set u | u in uu;
    case true =>
      z := t !in set u | u in uu :: Id(u);
  }
}

lemma TestsWhereTriggersMatter<T>(t: T, uu: seq<T>) returns (z: bool)
  requires 10 <= |uu| && uu[4] == t
  ensures z
{
  if {
    case true =>
      z := 7 in set i | 0 <= i < 10;
    case true =>
      z := 8 in set k: nat | k < 10;
    case true =>
      // In the line below, auto-triggers should pick Even(m)
      z := 5 in set m | 0 <= m < 10 && Even(m) :: m + 1;
      // a necessary lemma:
      assert Even(4);
    case true =>
      z := t in set u | u in uu;
    case true =>
      z := t in set u | u in uu :: Id(u);
  }
}

function Id<T>(t: T): T { t }
predicate Even(x: int) { x % 2 == 0 }

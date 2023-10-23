// RUN: %dafny /compile:0 /print:"%t.print" /dprint:"%t.dprint" /printTooltips "%s" > "%t"
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
      z := t !in set u {:autotriggers false} | u in uu :: Id(u);
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
      z := t in set u {:autotriggers false} | u in uu :: Id(u);
  }
}

ghost function Id<T>(t: T): T { t }
ghost predicate Even(x: int) { x % 2 == 0 }

class Container<T> {
  ghost var Contents: set<T>
  var elems: seq<T>

  method Add(t: T)
    requires Contents == set x | x in elems
    modifies this
    ensures Contents == set x | x in elems
  {
    elems := elems + [t];
    Contents := Contents + {t};
  }
}

class IntContainer {
  ghost var Contents: set<int>
  var elems: seq<int>

  method Add(t: int)
    requires Contents == set x | x in elems
    modifies this
    ensures Contents == set x | x in elems
  {
    elems := elems + [t];
    Contents := Contents + {t};
  }
}

method UnboxedBoundVariables(si: seq<int>)
{
  var iii := set x | x in si;
  var ti := si + [115];
  var jjj := set y | y in ti;
  assert iii + {115} == jjj;

  var nnn := set n: nat | n in si;
  if forall i :: 0 <= i < |si| ==> 0 <= si[i] {
    assert nnn == iii;
  }
}


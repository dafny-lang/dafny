// RUN: %exits-with 2 %baredafny verify %args --type-system-refresh "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

ghost function f2(items: set<nat>): (r:nat)
  requires |items| > 0 {
    var item :| item in items;
    item
}

function f(items: set<nat>) : (r:nat)
requires |items| > 0 {
    //assume exists item :: item in items && forall other <- items :: item == other || item < other;
    //assert exists item Smallest()
    var item :| IsSmallest(items, item);
    item
}

predicate IsSmallest(s: set<nat>, item: nat) 
  requires item in s {
  m in s && forall y: nat :: y in s ==> m <= y
}

lemma Smallest(s: set<nat>) returns (m: nat)
  requires s != {}
  ensures m in s && IsSmallest(s, m)
  decreases s
{
  m :| m in s;
  if y: nat :| y in s && y < m {
    ghost var s' := s - {m};
    assert y in s';
    m := ThereIsASmallest(s');
  }
}

function smallest(items: set<nat>): (r: nat)
  requires |items| > 0

method m(items: set<nat>) returns (r:nat)
requires |items| > 0 {
    var item :| item in items;
    return item;
}
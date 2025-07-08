// RUN: %exits-with 2 %verify --type-system-refresh --general-newtypes --general-traits=full "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module DirectParents {
  trait SupportsAdd {
    function Add(x: int): int
  }

  newtype MySet extends SupportsAdd = set<int> {
    function Add(x: int): int {
      3 * |this| + 2 * x
    }
  }

  newtype AnotherSet = MySet {
  }

  newtype RepeatExtendsClause extends SupportsAdd = MySet {
  }

  method Test() {
    var m: MySet := {3, 9, 2, 3};
    var s := m.Add(2);
    assert s == 13;
    print s, "\n";

    var t: SupportsAdd := m;
    s := t.Add(2);
    assert s == 13;
    print s, "\n";

    var u: AnotherSet := {3, 9, 2, 3};
    t := u; // error: AnotherSet not (directly) assignable to SupportsAdd
    t := u as SupportsAdd; // error: AnotherSet not (directly) assignable to SupportsAdd
    var isIt := u is SupportsAdd; // error: AnotherSet not (directly) assignable to SupportsAdd
    t := u as MySet; // this is how ya do it
    s := u.Add(2) + t.Add(2);
    assert s == 26;
    print s, "\n";

    var r: RepeatExtendsClause := {3, 9, 2, 3};
    t := r;
    assert t == r as SupportsAdd;
    assert r is SupportsAdd;
    assert t == r as MySet;
    assert t is MySet;
    assert t is RepeatExtendsClause;
  }
}

// The following module is analogous to the ExtendsMustBeDirect module in traits/TraitsExtendingTraits.dfy
module MoreDirectParents {
  trait HasG {
    function G(): int
  }

  newtype A extends HasG = int { // yes, A does extend HasG
    function G(): int { 2 }
  }

  newtype B extends HasG = A { // yes, since A extends HasG, so does B
  }

  newtype C = int { // C quacks like a HasG, but does not declare "extends HasG"
    function G(): int { 2 }
  }

  newtype D extends HasG = C { // error: D does not declare G by itself and C is not declared to extend HasG
  }
}

module MissingMember {
  trait SupportsAdd {
    function Add(x: int): int
  }

  trait SupportsSubtract {
    function Subtract(x: int): int
  }

  newtype YesToAddButNotSubtract extends SupportsAdd, SupportsSubtract = set<int> { // error: type does not implement Subtract
    function Add(x: int): int {
      3 * |this| + 2 * x
    }
  }
}

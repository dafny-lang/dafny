module RelationExamples {

  import opened DafnyStdLibs.Relations

  lemma TestRelationProperties() {
    assert Reflexive<int>((a,b) => a == b);
    assert Irreflexive<int>((a,b) => a != b);
    assert Symmetric((a,b) => a && b);
    assert Asymmetric<int>((a,b) => a < b);
    assert AntiSymmetric<bool>((a,b) => a ==> b);
    assert Connected<int>((a,b) => a < b);
    assert StronglyConnected<int>((a,b) => a <= b);
    assert Transitive<int>((a,b) => a == b);
    assert TotalOrdering<int>((a,b) => a <= b);
    assert StrictTotalOrdering<int>((a,b) => a < b);

    var partialOrdering := (a: int, b: int) => !(a == 9 && b == 10) && a <= b;
    assert PartialOrdering<int>(partialOrdering);
    assert !partialOrdering(9,10) && !partialOrdering(10,9);
    assert !StronglyConnected(partialOrdering);

    assert TotalOrdering<int>((a,b) => a <= b);
    assert StrictTotalOrdering<int>((a,b) => a < b);

    assert EquivalenceRelation((a,b) => a % 2 == b % 2);
  }

  lemma TestElementProperties() {
    var xs := { 1, 2 };
    var lessEqual := (a,b) => a <= b;
    assert IsLeast(lessEqual, 1, xs);
    assert IsMinimal(lessEqual, 1, xs);
  }

  lemma TestSorting() {
    var xs := [1,2,3];
    var ys := [3,2,1];
    var lessEqual := (a,b) => a <= b;
    assert SortedBy(lessEqual, xs);
    assert ys[0] > ys[1];
    assert !SortedBy(lessEqual, ys);
  }
}

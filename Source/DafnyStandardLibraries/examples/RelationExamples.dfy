module RelationExamples {

  import opened Std.Relations

  const partialOrdering := (a: int, b: int) => !(a == 9 && b == 10) && a <= b
  lemma TestRelationProperties()
    ensures Reflexive<int>((a,b) => a == b)
    ensures Irreflexive<int>((a,b) => a != b)
    ensures Symmetric((a,b) => a && b)
    ensures Asymmetric<int>((a,b) => a < b)
    ensures AntiSymmetric<bool>((a,b) => a ==> b)
    ensures Connected<int>((a,b) => a < b)
    ensures StronglyConnected<int>((a,b) => a <= b)
    ensures Transitive<int>((a,b) => a == b)
    ensures TotalOrdering<int>((a,b) => a <= b)
    ensures StrictTotalOrdering<int>((a,b) => a < b)
    ensures !StronglyConnected(partialOrdering)
    ensures TotalOrdering<int>((a,b) => a <= b)
    ensures StrictTotalOrdering<int>((a,b) => a < b)
    ensures EquivalenceRelation((a,b) => a % 2 == b % 2)
  {
    assert !partialOrdering(9,10);
  }

  const lessEqualInt := (a: int, b) => a <= b
  lemma TestElementProperties()
    ensures IsLeast(lessEqualInt, 1, { 1, 2 })
    ensures IsMinimal(lessEqualInt, 1, { 1, 2 })
  {
  }

  lemma TestSorting()
    ensures SortedBy(lessEqualInt, [1, 2, 3])
    ensures !SortedBy(lessEqualInt, [3, 2, 1])
  {
    var ys := [3,2,1];
    assert ys[0] > ys[1];
  }
}


include "../test/dafnyRuntimeFeasibility.dfy"

module DafnyRuntimeFeasibilityTest {

  import opened FeasibilityImplementation

  method {:test} HappyPath() {
    EnsureSizeTLimitAboveMinimum();
    var a := NativeArray<int>.Make(5);
    for i: size_t := 0 to 5
      invariant a.Valid()
      invariant a.Length() == 5
      invariant fresh(a.Repr)
      invariant forall j | 0 <= j < i :: a.values[j].Set?
    {
      a.Update(i, i as int);
    }
    var frozen := a.Freeze(a.Length());
    var s: Sequence<int> := new ArraySequence(frozen);
    for i: size_t := 0 to 5
      invariant a.Valid()
    {
      var x := s.Select(i);
      expect x == i as int;
    }
  }
}

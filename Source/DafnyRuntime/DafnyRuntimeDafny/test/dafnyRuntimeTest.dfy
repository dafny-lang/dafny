
include "../src/dafnyRuntime.dfy"

abstract module DafnyRuntimeTests {

    import Dafny

    method {:test} HappyPath() {
        Dafny.EnsureSizeTLimitAboveMinimum();
        var a := Dafny.NativeArray.Make<int>(5);
        for i := 0 to 5 
            invariant a.Valid()
        {
            a.Update(i as Dafny.size_t, i);
        }
        var frozen := a.Freeze(a.Length());
        var s := new Dafny.ArraySequence(frozen);
        for i: Dafny.size_t := 0 to 5 
            invariant a.Valid()
        {
            expect s.Select(i) == i;
        }
    }
}
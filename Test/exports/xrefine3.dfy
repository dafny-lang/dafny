// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


module AlphaImpl {
    export reveals *

    export Spec provides Alpha, IsValid, Init

    type Alpha(00) = bool

    predicate IsValid(a:Alpha) {
        a
    }

    method Init() returns (a:Alpha)
        ensures IsValid(a);
    {
        a := true;
    }
}

module BetaImpl {
    export reveals *
    export Spec provides ASpec, Beta, IsValid, Init


    import ASpec = AlphaImpl`Spec

    import A = AlphaImpl
    type Beta = seq<ASpec.Alpha>

    predicate IsValid(b:Beta) {
        forall i :: 0 <= i < |b| ==> A.IsValid(b[i])
    }

    method Init(ays:seq<ASpec.Alpha>) returns (b:Beta) {
        b := ays;
    }
}

module MainImpl {
    export Spec provides Main

    import A = AlphaImpl`Spec
    import B = BetaImpl`Spec

    import ASpec = B.ASpec

    ghost method Test()
    {
       var a : A.Alpha;
       var b : ASpec.Alpha;
       var e := a == b;

    }

    method Main()
    {
        var a := A.Init();
        var ays := [a, a];
        assert forall i :: 0 <= i < |ays| ==> A.IsValid(ays[i]);
        var b := B.Init(ays);
        print "o hai!\n";
    }
}


// RUN: %dafny /ironDafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module AlphaSpec {
    type Alpha

    predicate IsValid(a:Alpha)

    method Init() returns (a:Alpha)
        ensures IsValid(a);
}

abstract module BetaSpec {
    type Beta
    import A as AlphaSpec

    predicate IsValid(b:Beta)

    method Init(ays:seq<A.Alpha>) returns (b:Beta)
        requires forall i :: 0 <= i < |ays| ==> A.IsValid(ays[i]);
        ensures IsValid(b);
}

module AlphaImpl exclusively refines AlphaSpec {
    type Alpha = bool    

    predicate IsValid(a:Alpha) { 
        a 
    }

    method Init() returns (a:Alpha)
        ensures IsValid(a);
    {
        a := true;
    }
}

module BetaImpl exclusively refines BetaSpec {
    import A = AlphaImpl
    type Beta = seq<A.Alpha>

    predicate IsValid(b:Beta) {
        forall i :: 0 <= i < |b| ==> A.IsValid(b[i])
    }

    method Init(ays:seq<A.Alpha>) returns (b:Beta) {
        b := ays;
    }
}

abstract module MainSpec {
    import A as AlphaSpec
    import B as BetaSpec

    method Main()
    {
        var a := A.Init();
        var ays := [a, a];
        assert forall i :: 0 <= i < |ays| ==> A.IsValid(ays[i]);
        var b := B.Init(ays);
        print "o hai!\n";
    }
}

module MainImpl exclusively refines MainSpec {
    import B = BetaImpl
    import A = AlphaImpl
}





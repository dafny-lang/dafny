// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"


module ProtocolImpl {
    export reveals *
    export Spec provides ProtoT, Init

    type ProtoT = bool

    predicate Init(p:ProtoT) { p }

    method orange(i:nat) returns (j:nat)
    {
        j := i + 1;
    }
}

module HostImpl {
    export reveals *
    export Spec provides HostT, foo, P

    import P = ProtocolImpl

    type HostT = int

    function method foo(h:HostT) : P.ProtoT
    {
        h != 0
    }

    method apple(i:nat) returns (j:nat)
    {
        j := i + 1;
    }
}

module MainImpl {
    export reveals *
    export Spec provides Test, HISpec, PISpec

    import HISpec = HostImpl`Spec
    import PISpec = ProtocolImpl`Spec

    import HI = HostImpl
    import PI = ProtocolImpl

    method Test(h1:HISpec.HostT, h2:HISpec.HostT)
        requires HISpec.foo(h1) == HISpec.foo(h2);
        requires PISpec.Init(HISpec.foo(h1))
    {
        var a := HI.foo(h1);
        print "HI.foo(h1) => ", a, "\n";
        var b := HI.foo(h2);
        print "HI.foo(h2) => ", b, "\n";
        var i := PI.orange(1);
        print "PI.orange(1) => ", i, "\n";
        var j := HI.apple(2);
        print "PI.apple(2) => ", j, "\n";
    }

    method Main()
    {
        Test(-1, 1);
    }
}





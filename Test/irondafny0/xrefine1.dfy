// RUN: %dafny /ironDafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

abstract module ProtocolSpec {
    type ProtoT

    predicate Init(p:ProtoT)
}

abstract module HostSpec {
    type HostT
    import P : ProtocolSpec

    function method foo(h:HostT) : P.ProtoT
}

module ProtocolImpl exclusively refines ProtocolSpec {
    type ProtoT = bool    

    predicate Init(p:ProtoT) { !p }

    method orange(i:nat) returns (j:nat)
    {
        j := i + 1;
    }
}

module HostImpl exclusively refines HostSpec {
    import P = ProtocolImpl

    type HostT = int

    function method foo(h:HostT) : P.ProtoT
    {
        h > 0
    }

    method apple(i:nat) returns (j:nat)
    {
        j := i + 1;
    }
}

abstract module MainSpec {
    import HI : HostSpec
    import PI : ProtocolSpec

    method Test(h1:HI.HostT, h2:HI.HostT) 
        requires HI.foo(h1) == HI.foo(h2);
        requires PI.Init(HI.foo(h1))
}

module MainImpl exclusively refines MainSpec {
    import HI = HostImpl
    import PI = ProtocolImpl
    
    method Test(h1:HI.HostT, h2:HI.HostT) 
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





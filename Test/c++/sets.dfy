newtype{:uint32iveType "uint"} uint32 = i:int | 0 <= i < 0x100000000

method Test(name:string, b:bool) 
  requires b;
{
  if b {
    print name, ": This is expected\n";
  } else {
    print name, ": This is unexpected\n";
  }
}

method Basic() {
  var s:set<uint32> := {1, 2, 3, 4};
  var t:set<uint32> := {1, 2, 3, 4};

  Test("Identity", s == s);
  Test("ValuesIdentity", s == t);
  Test("DiffIdentity", s - {1} == t - {1});
  Test("DiffIdentitySelf", s - {2} != s - {1});
  Test("ProperSubsetIdentity", !(s < s));
  Test("ProperSubset", !(s < t));
  Test("SelfSubset", s <= s);
  Test("OtherSubset", t <= s && s <= t);
  Test("UnionIdentity", s + s == s);
}

/*
method ValueEquality() {
    var m0:seq<uint32> := [1, 2, 3];
    var m1:seq<uint32> := m0[1..];
    var m2:seq<uint32> := [2, 3];
    if m1 == m2 {
        print "ValueEquality: This is expected\n";
    } else {
        print "ValueEquality: This is unexpected\n";
        assert false;
    }
}

method Contains() {
    var m1:seq<uint32> := [1];
    var m2:seq<uint32> := [1, 2];
    var m3:seq<uint32> := [1, 2, 3];
    var m3identical:seq<uint32> := [1, 2, 3];
    var mm := [m1, m3, m1];

    if m1 in mm {
        print "Membership 1: This is expected\n";
    } else {
        print "Membership 1: This is unexpected\n";
        assert false;
    }
    if m2 in mm {
        print "Membership 2: This is unexpected\n";
        assert false;
    } else {
        print "Membership 2: This is expected\n";
    }
    if m3 in mm {
        print "Membership 3: This is expected\n";
    } else {
        print "Membership 3: This is unexpected\n";
        assert false;
    }
    if m3identical in mm {
        print "Membership 3 value equality: This is expected\n";
    } else {
        print "Membership 3 value equality: This is unexpected\n";
        assert false;
    }
}

method Main() {
    Basic();
    ValueEquality();
    Contains();
}
*/

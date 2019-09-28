newtype{:uint32iveType "uint"} uint32 = i:int | 0 <= i < 0x100000000

method Test(name:string, b:bool) 
  requires b;
{
  if b {
    print name, ": This is expected\n";
  } else {
    print name, ": This is *** UNEXPECTED *** !!!!\n";
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
  Test("Membership", 1 in s);
  Test("NonMembership1", !(5 in s));
  Test("NonMembership2", !(1 in (s - {1})));
}

method SetSeq() {
  var m1:seq<uint32> := [1];
  var m2:seq<uint32> := [1, 2];
  var m3:seq<uint32> := [1, 2, 3];
  var m4:seq<uint32> := [1, 2, 3, 4];
  var n1:seq<uint32> := [1];
  var n2:seq<uint32> := [1, 2];
  var n3:seq<uint32> := [1, 2, 3];

  var s1:set<seq<uint32>> := { m1, m2, m3 };
  var s2:set<seq<uint32>> := s1 - { m1 };

  Test("SeqMembership1", m1 in s1);
  Test("SeqMembership2", m2 in s1);
  Test("SeqMembership3", m3 in s1);
  Test("SeqNonMembership1", !(m1 in s2));
  Test("SeqNonMembership2", !(m4 in s1));
  Test("SeqNonMembership3", !(m4 in s2));

  Test("SeqMembershipValue1", n1 in s1);
  Test("SeqMembershipValue2", n2 in s1);
  Test("SeqMembershipValue3", n3 in s1);
}

method SetComprehension(s:set<uint32>)
  requires forall i :: 0 <= i < 10 ==> i in s;
  requires |s| == 10;
{
  /*
  var s:set<uint32> := set x:uint32 | 0 <= x < 10;
  Test("SetComprehensionMembership1", 1 in s);
  Test("SetComprehensionMembership2", 2 in s);
  Test("SetComprehensionMembership9", 9 in s);
  Test("SetComprehensionNonMembership1", !(11 in s));
  */

  var t:set<uint32> := set y:uint32 | y in s;
  Test("SetComprehensionInEquality", t == s);
  Test("SetComprehensionInMembership", 0 in t);
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
*/

method Main() {
    Basic();
    SetSeq();
    var s := { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
    SetComprehension(s);
}

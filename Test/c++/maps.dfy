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
  var s:map<uint32,uint32> := map[1 := 0, 2 := 1, 3 := 2, 4 := 3];
  var t:map<uint32,uint32> := map[1 := 0, 2 := 1, 3 := 2, 4 := 3];

  Test("Identity", s == s);
  Test("ValuesIdentity", s == t);
  Test("KeyMembership", 1 in s);
  Test("Value1", s[1] == 0);
  Test("Value2", t[2] == 1);

  var u := s[1 := 42];
  Test("Update Inequality", s != u);
  Test("Update Immutable 1", s == s);
  Test("Update Immutable 2", s[1] == 0);
  Test("Update Result", u[1] == 42);
  Test("Update Others", u[2] == 1);

  var s_keys := s.Keys;
  var t_keys := t.Keys;
  Test("Keys equal", s_keys == t_keys);
  Test("Keys membership 1", 1 in s_keys);
  Test("Keys membership 2", 2 in s_keys);
  Test("Keys membership 3", 3 in s_keys);
  Test("Keys membership 4", 4 in s_keys);
}

/*
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
}

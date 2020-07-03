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

datatype map_holder = map_holder(m:map<bool, bool>)

method Basic() {
  var f:map_holder;
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


method Main() {
    Basic();
}

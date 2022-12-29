// RUN: %baredafny verify %args "%s" > "%t"
// RUN: %baredafny run %args --no-verify --target=cs "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=js "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=go "%s" >> "%t"
// RUN: %baredafny run %args --no-verify --target=java "%s" >> "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var s := { 1,9,3,7,5};
  m(s);
  mp(map[ 1:= 3, 3:= 5]);
}


method m(s: set<int>) {
  var ss := s;
  while ss != {}
    decreases |ss|
  {
    var i: int :| i in ss;
    ss := ss - {i};
    print i, "\n";
  }
}

method mp(m: map<int,int>)
{
  var items := m.Items;
  while items != {}
    decreases |items|
  {
    var item :| item in items;
    items := items - { item };
    print item.0, " ", item.1, "\n";
  }
}

method mpi(m: imap<int,int>)
{
  var items: iset<(int,int)> := m.Items;
  var keys: iset<int> := m.Keys;
  var vals: iset<int> := m.Values;
}

method mseq(s: seq<int>) {
  var i: int := 0;
  var sum: int := 0;
  while i < |s|
    decreases |s| - i
  {
    sum := sum + s[i];
    i := i + 1;
  }
}

method marr(s: array<int>) {
  var i: int := 0;
  var sum: int := 0;
  while i < s.Length
    decreases s.Length - i
  {
    sum := sum + s[i];
    i := i + 1;
  }

  var rev := new int[s.Length];
  forall i | 0 <= i < s.Length {
    rev[i] := s[s.Length-i-1];
  }
}

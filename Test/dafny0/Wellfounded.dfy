// RUN: %baredafny run %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Main() {
  var d := Int(10);
  d := Set({d});
  d := Seq([d,d,d]);
  d := Multiset(multiset{d,d});
  d := Map0(map[d := 40]);
  d := Map1(map[15 := d]);
  d := IMap1(imap[15 := d]);

  var a1 := Map1(map[22 := d]);
  var a2 := IMap1(imap[23 := d]);

  var r;
  r := M(d, d);
  print "M(d, d) = ", r, "\n";
  r := M(a1, d);
  print "M(a1, d) = ", r, "\n";
  r := M(a2, d);
  print "M(a2, d) = ", r, "\n";
}

datatype Dt =
  | Int(int)
  | Set(set<Dt>)
  // | ISet(iset<Dt>) //  This definition is not allowed because Dt appears in a non-strict/lax position
  | Seq(seq<Dt>)
  | Multiset(multiset<Dt>)
  | Map0(map<Dt,int>)
  | Map1(map<int,Dt>)
  // | IMap0(imap<Dt,int>) //  This definition is not allowed because Dt appears in a non-strict/lax position
  | IMap1(imap<int,Dt>)

method M(d: Dt, d': Dt) returns (r: int)
  decreases d
{
  match d
  case Int(x) =>
    r := x;
  case Set(s) =>
    if e :| e in s {
      r := M(e, d');
    }
  case Seq(s) =>
    if * {
      r := N(s, d');
    } else if j :| 0 <= j < |s| {
      r := M(s[j], d');
    }
  case Multiset(s) =>
    if e :| e in s {
      r := M(e, d');
    }
  case Map0(m) =>
    if e :| e in m.Keys {
      r := M(e, d');
    }
  case Map1(m) =>
    if 15 in m.Keys {
      r := M(m[15], d');
    } else if d' in m.Values {
      r := M(d', d');
    }
  case IMap1(m) =>
    if 15 in m.Keys {
      r := M(m[15], d');
    } else if d' in m.Values {
      r := M(d', d');
    }
}

method N(s: seq<Dt>, d': Dt) returns (r: int)
  decreases s
{
  if j :| 0 <= j < |s| {
    r := M(s[j], d');
  }
}

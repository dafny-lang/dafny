// RUN: %exits-with 2 %dafny /print:"%t.print" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

newtype Lower = x | -2 <= x

newtype NR = r | -2.0 <= r <= 5.4

method Main()
{
  var b;
  b := forall o': Lower :: true ==> P(o' as int);  // error: cannot find finite range
  b := forall r: real :: 0.0 <= r <= 100.0 ==> Q(r);  // error: cannot find finite range
  b := forall r': NR :: true ==> Q(r' as real);  // error: cannot find finite range
}

predicate P(x: int)
{
  x == 157
}

predicate Q(r: real)
{
  r / 2.0 <= r
}

method ForallStmt_Int()
{
  var a := new real[8](i => i as real - 4.0);
  var b := new real[8];
  var c := new bool[8];
  forall i | 6 <= 2*(i+3) && i < a.Length {  // error: heuristics too weak to detect this range is compilable
    b[7-i] := a[i] + 4.0;
  }
  forall i | true {  // error: non-compilable range
    c[if 0 <= i < a.Length then i else 0] :=
      var j := if 0 <= i < a.Length then i else 0;
      a[j] < b[j];
  }
}

method ForallStmt_Objects(ks: set<K>)
  requires ks != {}
  modifies ks
{
  print "max: ", Max(ks), "\n";
  forall k | k in ks {
    k.u := 57;
  }
  print "max: ", Max(ks), "\n";

  var myK := new K;
  forall k: K | true {  // error: non-compilable range
    (if k in ks then k else myK).u := 57;
  }
}

class K {
  var u: int
}

function Max(ks: set<K>): int
  requires ks != {}
  reads ks
{
  MaxExists(ks);
  var k :| k in ks && forall m :: m in ks ==> m.u <= k.u;
  k.u
}

lemma MaxExists(ks: set<K>)
  requires ks != {}
  ensures exists k :: k in ks && forall m :: m in ks ==> m.u <= k.u
{
  var k :| k in ks;
  if m :| m in ks && k.u < m.u {
    assert |{k,m}| == 2;
    MaxExists(ks - {k});
  }
}

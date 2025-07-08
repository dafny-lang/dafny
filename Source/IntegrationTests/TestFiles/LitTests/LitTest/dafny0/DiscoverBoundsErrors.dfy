// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"


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

predicate LessThanFour(x: int) {
  x < 4
}

ghost function PlusOne(x: int): int {
  x + 1
}

method EnumerateOverInfiniteCollections() {
  var s := {3, 3, 3, 5};
  var l;
  // Once, the TermLeft of map comprehensions was not checked for ghost-ness. Thus, the following assignment
  // had been allowed by the resolver, which caused the compiler to emit malformed target code. (Oddly enough,
  // when using the same RHS as an initializing assignment, the ghost-ness was detected and caused the variable
  // to become auto-ghost which means an error is reported about the print statement not being compilable.)
  l := map x | x in s && LessThanFour(x) :: PlusOne(x) := x;
  print l, "\n"; // map[3 := 3]
}

newtype MyInt = x: int | -0x8000_0000 <= x

method Casts() {
  // casts around just the variable is fine, but around any other expression is more complicated (so we don't handle it, for now)
  print forall x: MyInt :: -12 <= x && (x as int - 2) as int < 0 ==> LessThanFour(x as int); // error: dunno how to compile
  print forall x: MyInt :: 12 <= x && (x as int - 20) as int < 0 ==> LessThanFour(x as int); // error: dunno how to compile
  print forall x: int :: 11 <= x && (x as real - 20.0) as int < 0 ==> LessThanFour(x as int); // error: dunno how to compile
}

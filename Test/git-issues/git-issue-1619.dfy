// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

predicate method {:opaque} P<W>(w: W) {
  true
}

method GimmieOne<W>(s: seq<W>) returns (c: W)
  requires s != []
{
  return s[0];
}

method M0<W>(s: seq<W>) returns (ghost r: W)
{
  var b := exists w: W :: P(w);
  ghost var w: W :| b ==> P(w); // error: because W may be empty
  if s != [] {
    var cand0: W;
    cand0 := GimmieOne(s);
  }
  return w;
}

method M0Init<W>(s: seq<W>) returns (ghost r: W)
{
  var b := exists w: W :: P(w);
  ghost var w: W :| b ==> P(w); // error: because W may be empty
  if s != [] {
    var cand0: W := GimmieOne(s);
  }
  return w;
}

method M1<W>(s: seq<W>) returns (ghost r: W)
{
  var b := exists w: W :: P(w);
  ghost var w: W :| b ==> P(w); // error: because W may be empty
  if s != [] {
    var xyz: int, cand1: W;
    xyz, cand1 := 15, s[0];
  }
  return w;
}

method M1Init<W>(s: seq<W>) returns (ghost r: W)
{
  var b := exists w: W :: P(w);
  ghost var w: W :| b ==> P(w); // error: because W may be empty
  if s != [] {
    var xyz: int, cand1: W := 15, s[0];
  }
  return w;
}

method Correct0<W(00)>(s: seq<W>) returns (ghost r: W)
{
  var b := exists w: W :: P(w);
  ghost var w: W :| b ==> P(w);
  return w;
}

method Correct1<W(0)>(s: seq<W>) returns (ghost r: W)
{
  var b := exists w: W :: P(w);
  ghost var w: W :| b ==> P(w);
  return w;
}

datatype Option<X> = None | Some(X)

method Correct2<W>(s: seq<W>) returns (ghost r: Option<W>)
{
  if s == [] {
    return None;
  }
  var b := exists w: W :: P(w);
  ghost var nonempty: W := s[0]; // this leads the verifier to see that W must be nonempty after all
  ghost var w: W :| b ==> P(w);
  return Some(w);
}

method Correct3<W>(s: seq<W>) returns (ghost r: Option<W>)
{
  if s == [] {
    return None;
  }
  var b := exists w: W :: P(w);
  ghost var w: W := s[0]; // assign w a throwaway value, just for long enough to show that W is nonempty after all
  w :| b ==> P(w);
  return Some(w);
}

method Correct4<W(00)>(s: seq<W>) returns (ghost r: Option<W>)
{
  var b := exists w: W :: P(w);
  ghost var w: W :| b ==> P(w);
  return Some(w);
}

method Correct5<W(0)>(s: seq<W>) returns (ghost r: Option<W>)
{
  var b := exists w: W :: P(w);
  ghost var w: W :| b ==> P(w);
  return Some(w);
}

// ------------- make sure ":= *", ":| true", and uninitialized work correctly

method NoInit()
{
  var i: nat, j: nat;
  assert 0 <= i;
}

method HavocOne()
{
  var i: nat;
  i := *;
  assert 0 <= i;
}

method HavocMultiple()
{
  var i: nat, j: nat;
  i, j := *, 3;
  assert 0 <= i;
}

method SuchThatOne()
{
  var i: nat;
  i :| true;
  assert 0 <= i;
}

method SuchThatMultiple()
{
  var i: nat, j: nat;
  i, j :| j == 3;
  assert 0 <= i;
}

method CallNatNat()
{
  var i: nat, j: nat := NatNat();
  assert 0 <= i;
}
method NatNat() returns (x: nat, y: nat) {
}

predicate F(p: seq<int>)

method F0() {
  var p: seq<int>, other: int := *, *;
  assume F(p);
  assert exists p :: F(p);
}

method F1() {
  var p: seq<int> := *;
  assume F(p);
  assert exists p :: F(p);
}

type MaybeEmpty
predicate G(m: MaybeEmpty)

method G0() {
  var m: MaybeEmpty, other: int := *, *;
  assume G(m); // error: use before definition
  assert exists m :: G(m); // error: cannot prove assertion
}

method G1() {
  var m: MaybeEmpty := *;
  assume G(m); // error: use before definition
  assert exists m :: G(m);
}

method H<U(00)>() {
  var u: U := *;
  var uu := u; // error: use before definition
}

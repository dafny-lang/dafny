// RUN: %exits-with 4 %dafny "%s" > "%t"
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
  assume G(m); // error: use before definition (note, execution continues after this check under the assumption that m really has been assigned)
  assert exists m2 :: G(m2); // this passes (see previous line)
  assert false; // error: assertion violation
}

method G1() {
  var m: MaybeEmpty := *;
  assume G(m); // error: use before definition
  assert exists m :: G(m);
  assert false; // error: assertion violation
}

method H<U(00)>() {
  var u: U := *;
  var uu := u; // error: use before definition
}

// more tests ---------------------------

type NonEmpty = x: int | 2 <= x < 7 ghost witness 6
type PossiblyEmpty = x: int | 2 <= x < 7 witness *
predicate MaybeOrMaybeNot(x: int)
type AlsoPossiblyEmpty = x: int | MaybeOrMaybeNot(x) witness *

method HavocSingleVar(n: nat) {
  var p: PossiblyEmpty;

  // The following "*" assignment does not fulfill any definite-assignment obligations. That
  // is, even after this "*" assignment, "p" is not considered to have been definitely
  // assigned.
  p := *;
  if * {
    assert p < 10; // error: use before definition
  }

  p := 3;
  // Since p has now been assigned, the "*" assignment to "p" in the next line will give
  // a value that's known to be of the type PossibleEmpty.
  p := *;
  assert p < 12;
}

method HavocMultipleVar(n: nat) {
  var x: NonEmpty;
  var p: PossiblyEmpty;

  // The following "*" assignments do not fulfill any definite-assignment obligations. That
  // is, even after these "*" assignments, neither "x" nor "p" is considered to have been
  // definitely assigned.
  x, p := *, *;
  if * {
    assert x < 9; // error: use before definition
    assert p < 10; // error: use before definition
  }

  x, p := 3, 3;
  // Since p has now been assigned, the "*" assignment to "p" in the next line will give
  // a value that's known to be of the type PossibleEmpty.
  x, p := *, *;
  assert x < 9;
  assert p < 12;
}

method AssignSuchSingleVar(n: nat) {
  var p: PossiblyEmpty;

  // An assign-such-that statement fulfills any definite-assignment obligations. However,
  // as usual, one has to prove that a value exists--which in this case follows from the
  // given range constraint (which the verifier studies, in order to build a helpful proof
  // obligation).
  p :| true;
  if * {
    assert p < 10;
  }
}

method AssignSuchMultipleVar(n: nat) {
  var x: NonEmpty;
  var p: PossiblyEmpty;

  // An assign-such-that statement fulfills any definite-assignment obligations. However,
  // as usual, one has to prove that a value exists--which in this case follows from the
  // given range constraints (which the verifier studies, in order to build helpful proof
  // obligations).
  x, p :| true;
  if * {
    assert x < 9;
    assert p < 10;
  }
}

method AssignSuchSingleVar'(n: nat) {
  var p: AlsoPossiblyEmpty;

  if * {
    assert MaybeOrMaybeNot(p); // error: use before definition
  } else {
    // An assign-such-that statement fulfills any definite-assignment obligations. However,
    // as usual, one has to prove that a value exists--which in this case cannot be done,
    // since nothing is known about the constraint MaybeOrMaybeNot.
    p :| true; // error: cannot establish existence of a value for p
    if * {
      // if we ever get here, then p has been definitely assigned and thus the constraint holds
      assert MaybeOrMaybeNot(p);
    }
  }
}

method AssignSuchMultipleVar'(n: nat) {
  var x: NonEmpty;
  var p: AlsoPossiblyEmpty;

  if * {
    assert MaybeOrMaybeNot(p); // error: use before definition
  } else {
    // An assign-such-that statement fulfills any definite-assignment obligations. However,
    // as usual, one has to prove that a value exists--which in this case cannot be done,
    // since nothing is known about the constraint MaybeOrMaybeNot.
    x, p :| true; // error: cannot establish existence of a value (for p)
    if * {
      // if we ever get here, then p has been definitely assigned and thus the constraints hold
      assert x < 9;
      assert MaybeOrMaybeNot(p);
    }
  }
}

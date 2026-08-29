// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s"

// Dafny's "==" on fp64 is value identity in the SMT FloatingPoint sort:
//   - there is one NaN, so NaN == NaN
//   - +0.0 and -0.0 are two different values, so +0.0 != -0.0
// This is deliberately not IEEE fp.eq, which says the opposite of both. IEEE equality is
// available as fp64.Equal.
//
// The two halves of this file are checked against each other. Each "assert" is what the verifier
// proves; each "print" is what the compiled program does. If the runtime ever stops agreeing with
// the verifier, either verification fails here or the expected-output diff does.
//
// Every "==" below is in compiled code and needs no precondition, the compiled types
// implementing value identity rather than C#'s IEEE "==".

method Reflexivity() {
  var one: fp64 := 1.0;
  var nan := fp64.NaN;
  var inf := fp64.PositiveInfinity;

  assert one == one;
  assert nan == nan;   // one NaN, so equality is reflexive here too
  assert inf == inf;
  print "1.0 == 1.0: ", one == one, "\n";
  print "NaN == NaN: ", nan == nan, "\n";
  print "+Inf == +Inf: ", inf == inf, "\n";
}

method DistinctValues() {
  var one: fp64 := 1.0;
  var two: fp64 := 2.0;
  var nan := fp64.NaN;
  var inf := fp64.PositiveInfinity;
  var ninf := fp64.NegativeInfinity;

  assert one != two;
  assert one != nan;
  assert inf != ninf;
  print "1.0 == 2.0: ", one == two, "\n";
  print "1.0 == NaN: ", one == nan, "\n";
  print "+Inf == -Inf: ", inf == ninf, "\n";
}

method SignedZerosAreDistinct() {
  var pos: fp64 := 0.0;
  var neg: fp64 := -0.0;

  assert pos != neg;
  assert pos.IsZero && neg.IsZero;
  assert neg.IsNegative && !pos.IsNegative;
  print "+0.0 == -0.0: ", pos == neg, "\n";
  print "+0.0 == +0.0: ", pos == 0.0, "\n";
  print "-0.0 is zero and negative: ", neg.IsZero, " ", neg.IsNegative, "\n";
}

// fp64.Equal is IEEE fp.eq, and disagrees with "==" on precisely the two special cases.
method IeeeEquality() {
  var pos: fp64 := 0.0;
  var neg: fp64 := -0.0;
  var nan := fp64.NaN;
  var one: fp64 := 1.0;

  assert fp64.Equal(pos, neg);      // IEEE: the zeros are equal
  assert !fp64.Equal(nan, nan);     // IEEE: NaN is equal to nothing
  assert fp64.Equal(one, one);
  print "fp64.Equal(+0.0, -0.0): ", fp64.Equal(pos, neg), "\n";
  print "fp64.Equal(NaN, NaN): ", fp64.Equal(nan, nan), "\n";
  print "fp64.Equal(1.0, 1.0): ", fp64.Equal(one, one), "\n";
}

// One relation in both worlds, so a comparison moves freely between spec and code.
method GhostAndCompiledAgree(x: fp64, y: fp64) {
  ghost var spec := x == y;
  var compiled := x == y;
  assert compiled == spec;
}

method Disequality() {
  var one: fp64 := 1.0;
  var nan := fp64.NaN;
  print "1.0 != 2.0: ", one != 2.0, "\n";
  print "NaN != NaN: ", nan != nan, "\n";
  print "!fp64.Equal(1.0, NaN): ", !fp64.Equal(one, nan), "\n";
}

// Collections and datatypes key on the same notion of equality, in compiled code as in ghost code.
method Collections() {
  var s: set<fp64> := {0.0, -0.0, fp64.NaN};
  assert |s| == 3;
  print "|{+0.0, -0.0, NaN}|: ", |s|, "\n";

  var zeros: set<fp64> := {0.0};
  var negZeros: set<fp64> := {-0.0};
  assert zeros != negZeros;
  print "{+0.0} == {-0.0}: ", zeros == negZeros, "\n";

  var nans: set<fp64> := {fp64.NaN, fp64.NaN};
  assert |nans| == 1;
  print "|{NaN, NaN}|: ", |nans|, "\n";

  var m: map<fp64, int> := map[0.0 := 1, -0.0 := 2];
  assert |m| == 2;
  print "|map[+0.0 := 1, -0.0 := 2]|: ", |m|, ", m[+0.0]=", m[0.0], "\n";

  var a: seq<fp64> := [1.0, fp64.NaN];
  print "[1.0, NaN] == [1.0, NaN]: ", a == [1.0, fp64.NaN], "\n";
}

datatype Wrapper = Wrapper(value: fp64)
datatype NestedWrapper = NestedWrapper(values: set<fp64>)

method Datatypes() {
  assert Wrapper(fp64.NaN) == Wrapper(fp64.NaN);
  assert Wrapper(0.0) != Wrapper(-0.0);
  print "Wrapper(NaN) == Wrapper(NaN): ", Wrapper(fp64.NaN) == Wrapper(fp64.NaN), "\n";
  print "Wrapper(+0.0) == Wrapper(-0.0): ", Wrapper(0.0) == Wrapper(-0.0), "\n";
  print "NestedWrapper({1.0}) == NestedWrapper({1.0}): ",
        NestedWrapper({1.0}) == NestedWrapper({1.0}), "\n";
}

// Equality is usable in specifications without side conditions.
function SameValue(x: fp64, y: fp64): bool {
  x == y
}

lemma EqualityIsReflexive(x: fp64)
  ensures x == x
{
}

method Main() {
  Reflexivity();
  DistinctValues();
  SignedZerosAreDistinct();
  IeeeEquality();
  Disequality();
  Collections();
  Datatypes();
}

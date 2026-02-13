// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// fp32 equality tests - verifies that == works correctly for floating-point
//
// Key rules:
// - In ghost code: == always works (mathematical equality)
// - In compiled code: == requires excluding NaN and different-signed zeros
// - For collections/datatypes with fp32: == not allowed in compiled code
// - For IEEE 754 behavior: use fp32.Equal() instead
//
// Expecting 15 errors (marked with ERROR in comments)

// PART 1: Ghost vs Compiled Contexts

// Ghost code: == always works (mathematical equality)
ghost method TestGhostEquality(x: fp32, y: fp32) {
  assert x == x;  // Always true - even for NaN
  var b := x == y;  // No restrictions
}

// Compiled code: == needs preconditions
method TestCompiledEqualityNoCheck(x: fp32, y: fp32) returns (result: bool) {
  result := x == y;  // ERROR: needs preconditions
}

// Just excluding NaN isn't enough
method TestCompiledEqualityWithNaNCheck(x: fp32, y: fp32) returns (result: bool)
  requires !x.IsNaN && !y.IsNaN
{
  result := x == y;  // ERROR: also need signed zero check
}

// Complete preconditions for ==
method TestCompiledEqualityFull(x: fp32, y: fp32) returns (result: bool)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)
{
  result := x == y;  // OK: both NaN and ±0 handled
}

// Control flow can satisfy preconditions
method TestControlFlow(x: fp32, y: fp32) returns (result: bool) {
  if x.IsNaN || y.IsNaN {
    return false;
  }
  if x.IsZero && y.IsZero && x.IsNegative != y.IsNegative {
    return false;
  }
  result := x == y;  // OK: conditions checked above
}

// PART 2: IEEE 754 Equality

// IEEE equality via fp32.Equal - no preconditions needed
method TestIEEEEquality(x: fp32, y: fp32) returns (result: bool) {
  result := fp32.Equal(x, y);  // Always allowed
  // IEEE rules: NaN != NaN, +0 == -0
}

// IEEE behavior examples
method TestIEEEEqualityMethod() {
  var pos_zero: fp32 := 0.0;
  var neg_zero: fp32 := -0.0;
  var nan := fp32.NaN;

  var ieee_zeros := fp32.Equal(pos_zero, neg_zero);
  var ieee_nan := fp32.Equal(nan, nan);

  assert ieee_zeros;    // IEEE: +0 == -0
  assert !ieee_nan;     // IEEE: NaN != NaN
}

// Why +0 == -0 isn't allowed with ==
method TestBitwiseWithPreconditions() {
  var pos_zero: fp32 := 0.0;
  var neg_zero: fp32 := -0.0;

  if !pos_zero.IsNaN && !neg_zero.IsNaN &&
     !(pos_zero.IsZero && neg_zero.IsZero && pos_zero.IsNegative != neg_zero.IsNegative) {
    var bitwise_zeros := pos_zero == neg_zero;  // Unreachable
  }
}

// NaN comparison always fails
method TestNaNEquality() {
  var nan := fp32.NaN;
  var bad_nan_eq := nan == nan;  // ERROR: NaN not allowed
}

// Inequality needs same preconditions
method TestInequality(x: fp32, y: fp32) returns (result: bool)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)
{
  result := x != y;  // OK: same rules as ==
}

// Inequality without preconditions also fails
method TestInequalityError(x: fp32, y: fp32) returns (result: bool) {
  result := x != y;  // ERROR: needs same preconditions as ==
}

// PART 3: Collections and Datatypes

// Set equality not allowed in compiled code
method TestSetEquality() {
  var s1: set<fp32> := {1.0, 2.0, 3.0};
  var s2: set<fp32> := {1.0, 2.0, 3.0};
  var eq := s1 == s2;  // ERROR: sets with fp32
}

// Sequence equality also not allowed
method TestSequenceEquality() {
  var seq1: seq<fp32> := [1.0, 2.0];
  var seq2: seq<fp32> := [1.0, 2.0];
  var seq_eq := seq1 == seq2;  // ERROR: sequences with fp32
}

// But collections work fine in ghost code
ghost method TestCollectionsGhost() {
  var s1 := {1.0, 2.0, 3.0};
  var s2 := {1.0, 2.0, 3.0};
  assert s1 == s2;  // OK in ghost

  var seq1 := [1.0, 2.0];
  var seq2 := [1.0, 2.0];
  assert seq1 == seq2;  // OK in ghost

  // Even with NaN
  var nan := fp32.NaN;
  var s3 := {nan};
  assert s3 == s3;  // OK: reflexive in ghost

  // But +0 and -0 are different values
  var s4: set<fp32> := {0.0};
  var s5: set<fp32> := {-0.0};
  assert s4 != s5;  // Different sets
}

// Ghost variables can use collection equality
method TestGhostSetEquality() {
  var s1 := {1.0, 2.0};
  var s2 := {1.0, 2.0};

  ghost var ghost_eq := s1 == s2;  // OK: ghost variable
  assert ghost_eq;
}

// Functions need preconditions too
function SafeEqual(x: fp32, y: fp32): bool
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)
{
  x == y  // OK with preconditions
}

// Lemmas are ghost - no restrictions
lemma EqualityIsReflexiveInGhost(x: fp32)
  ensures x == x  // Always true in ghost
{
}

// Specifications can use == with preconditions
method TestSpecificationWF(x: fp32, y: fp32)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)
  requires x == y  // OK with preconditions
  ensures x == y   // OK with preconditions
{
}

// Datatypes with fp32 fields
datatype Container = Container(value: fp32)

method TestDatatype() {
  var c1 := Container(1.0);
  var c2 := Container(1.0);
  var result := c1 == c2;  // ERROR: datatype with fp32
}

// Ghost datatype equality works
ghost method TestDatatypeGhost() {
  var c1 := Container(1.0);
  var c2 := Container(1.0);
  assert c1 == c2;  // OK in ghost

  var c3 := Container(fp32.NaN);
  assert c3 == c3;  // OK: reflexive
}

// Nested fp32 also rejected
datatype Nested = Nested(s: set<fp32>)

method TestNestedDatatype() {
  var n1 := Nested({1.0});
  var n2 := Nested({1.0});
  var eq := n1 == n2;  // ERROR: nested fp32
}

// IEEE special values
method TestIEEESpecialCases() {
  var pos_zero: fp32 := 0.0;
  var neg_zero: fp32 := -0.0;
  var pos_inf := fp32.PositiveInfinity;
  var neg_inf := fp32.NegativeInfinity;
  var nan := fp32.NaN;

  // Store IEEE equality results in compiled variables
  var zeros_equal := fp32.Equal(pos_zero, neg_zero);
  var nan_equal := fp32.Equal(nan, nan);
  var inf_self_equal := fp32.Equal(pos_inf, pos_inf);
  var infs_equal := fp32.Equal(pos_inf, neg_inf);

  // Verify the IEEE semantics in ghost assertions
  assert zeros_equal;      // +0 == -0 (IEEE)
  assert !nan_equal;       // NaN != NaN (IEEE)
  assert inf_self_equal;   // +∞ == +∞
  assert !infs_equal;      // +∞ != -∞
}

// Ghost vs compiled can differ
method TestMixedContexts(x: fp32, y: fp32) {
  ghost var ghost_eq := x == y;  // Always defined

  if !x.IsNaN && !y.IsNaN && !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative) {
    var compiled_eq := x == y;  // Needs preconditions
    // When both are defined, they agree on the result
    assert compiled_eq == ghost_eq;
  }
  // But ghost_eq works for NaN and ±0 cases where compiled_eq cannot be used
}

method TestMainBitwise() {
  var pos_zero: fp32 := 0.0;
  var neg_zero: fp32 := -0.0;

  var bitwise_eq := pos_zero == neg_zero;  // ERROR: ±0 check fails
}

// PART 4: Soundness Tests

// Variable declarations are checked
method TestVariableDeclarationSoundness() {
  var s1: set<fp32> := {1.0, 2.0};
  var s2: set<fp32> := {1.0, 2.0};
  var eq := s1 == s2;  // ERROR: checked in declaration
  print eq;
}

// Assignments are checked too
method TestExplicitAssignmentError() {
  var s1: set<fp32> := {1.0, 2.0};
  var s2: set<fp32> := {1.0, 2.0};
  var eq: bool;
  eq := s1 == s2;  // ERROR: checked in assignment
}

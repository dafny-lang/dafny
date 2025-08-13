// RUN: %testDafnyForEachResolver --expect-exit-code=4 "%s"

// fp64 equality tests - verifies that == works correctly for floating-point
// 
// Key rules:
// - In ghost code: == always works (mathematical equality)
// - In compiled code: == requires excluding NaN and different-signed zeros
// - For collections/datatypes with fp64: == not allowed in compiled code
// - For IEEE 754 behavior: use fp64.Equal() instead
//
// Expecting 13 errors (marked with ERROR in comments)

// PART 1: Ghost vs Compiled Contexts

// Ghost code: == always works (mathematical equality)
ghost method TestGhostEquality(x: fp64, y: fp64) {
  assert x == x;  // Always true - even for NaN
  var b := x == y;  // No restrictions
}

// Compiled code: == needs preconditions
method TestCompiledEqualityNoCheck(x: fp64, y: fp64) returns (result: bool) {
  result := x == y;  // ERROR: needs preconditions
}

// Just excluding NaN isn't enough
method TestCompiledEqualityWithNaNCheck(x: fp64, y: fp64) returns (result: bool)
  requires !x.IsNaN && !y.IsNaN
{
  result := x == y;  // ERROR: also need signed zero check
}

// Complete preconditions for ==
method TestCompiledEqualityFull(x: fp64, y: fp64) returns (result: bool)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)
{
  result := x == y;  // OK: both NaN and ±0 handled
}

// Control flow can satisfy preconditions
method TestControlFlow(x: fp64, y: fp64) returns (result: bool) {
  if x.IsNaN || y.IsNaN {
    return false;
  }
  if x.IsZero && y.IsZero && x.IsNegative != y.IsNegative {
    return false; 
  }
  result := x == y;  // OK: conditions checked above
}

// PART 2: IEEE 754 Equality

// IEEE equality via fp64.Equal - no preconditions needed
method TestIEEEEquality(x: fp64, y: fp64) returns (result: bool) {
  result := fp64.Equal(x, y);  // Always allowed
  // IEEE rules: NaN != NaN, +0 == -0
}

// IEEE behavior examples
method TestIEEEEqualityMethod() {
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  var nan := fp64.NaN;
  
  var ieee_zeros := fp64.Equal(pos_zero, neg_zero);  // true (IEEE)
  var ieee_nan := fp64.Equal(nan, nan);              // false (IEEE)
}

// Why +0 == -0 isn't allowed with ==
method TestBitwiseWithPreconditions() {
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  
  if !pos_zero.IsNaN && !neg_zero.IsNaN && 
     !(pos_zero.IsZero && neg_zero.IsZero && pos_zero.IsNegative != neg_zero.IsNegative) {
    var bitwise_zeros := pos_zero == neg_zero;  // Unreachable
  }
}

// NaN comparison always fails
method TestNaNEquality() {
  var nan := fp64.NaN;
  var bad_nan_eq := nan == nan;  // ERROR: NaN not allowed
}

// Inequality needs same preconditions
method TestInequality(x: fp64, y: fp64) returns (result: bool)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)
{
  result := x != y;  // OK: same rules as ==
}

// PART 3: Collections and Datatypes

// Set equality not allowed in compiled code
method TestSetEquality() {
  var s1: set<fp64> := {1.0, 2.0, 3.0};
  var s2: set<fp64> := {1.0, 2.0, 3.0};
  var eq := s1 == s2;  // ERROR: sets with fp64
}

// Sequence equality also not allowed
method TestSequenceEquality() {
  var seq1: seq<fp64> := [1.0, 2.0];
  var seq2: seq<fp64> := [1.0, 2.0];
  var seq_eq := seq1 == seq2;  // ERROR: sequences with fp64
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
  var nan := fp64.NaN;
  var s3 := {nan};
  assert s3 == s3;  // OK: reflexive in ghost
  
  // But +0 and -0 are different values
  var s4: set<fp64> := {0.0};
  var s5: set<fp64> := {-0.0};
  assert s4 != s5;  // Different sets
}

// Ghost variables can use collection equality
method TestGhostSetEquality() {
  var s1 := {1.0, 2.0};
  var s2 := {1.0, 2.0};
  
  ghost var ghost_eq := s1 == s2;  // OK: ghost variable
  assert ghost_eq;
}

// Compiled variables cannot
method TestCompiledSetEquality() {
  var s1: set<fp64> := {1.0, 2.0};
  var s2: set<fp64> := {1.0, 2.0};
  
  var compiled_eq := s1 == s2;  // ERROR: compiled variable
}

// Functions need preconditions too
function SafeEqual(x: fp64, y: fp64): bool
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)
{
  x == y  // OK with preconditions
}

// Lemmas are ghost - no restrictions
lemma EqualityIsReflexiveInGhost(x: fp64)
  ensures x == x  // Always true in ghost
{
}

// Specifications can use == with preconditions
method TestSpecificationWF(x: fp64, y: fp64)
  requires !x.IsNaN && !y.IsNaN
  requires !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative)
  requires x == y  // OK with preconditions
  ensures x == y   // OK with preconditions
{
}

// Datatypes with fp64 fields
datatype Container = Container(value: fp64)

method TestDatatype() {
  var c1 := Container(1.0);
  var c2 := Container(1.0);
  var result := c1 == c2;  // ERROR: datatype with fp64
}

// Ghost datatype equality works
ghost method TestDatatypeGhost() {
  var c1 := Container(1.0);
  var c2 := Container(1.0);
  assert c1 == c2;  // OK in ghost
  
  var c3 := Container(fp64.NaN);
  assert c3 == c3;  // OK: reflexive
}

// Nested fp64 also rejected
datatype Nested = Nested(s: set<fp64>)

method TestNestedDatatype() {
  var n1 := Nested({1.0});
  var n2 := Nested({1.0});
  var eq := n1 == n2;  // ERROR: nested fp64
}

// IEEE special values
method TestIEEESpecialCases() {
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  var pos_inf := fp64.PositiveInfinity;
  var neg_inf := fp64.NegativeInfinity;
  var nan := fp64.NaN;
  
  assert fp64.Equal(pos_zero, neg_zero);  // +0 == -0 (IEEE)
  assert !fp64.Equal(nan, nan);           // NaN != NaN (IEEE)
  assert fp64.Equal(pos_inf, pos_inf);    // +∞ == +∞
  assert !fp64.Equal(pos_inf, neg_inf);   // +∞ != -∞
}

// Ghost vs compiled can differ
method TestMixedContexts(x: fp64, y: fp64) {
  ghost var ghost_eq := x == y;  // Always defined
  
  if !x.IsNaN && !y.IsNaN && !(x.IsZero && y.IsZero && x.IsNegative != y.IsNegative) {
    var compiled_eq := x == y;  // Needs preconditions
    // When both defined, they agree
    // But ghost works for NaN and ±0 cases too
  }
}

// Practical examples
method TestMainIEEE() {
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  
  var ieee_eq := fp64.Equal(pos_zero, neg_zero);
  print "IEEE: +0.0 == -0.0 is ", ieee_eq, "\n";  // prints true
}

method TestMainBitwise() {
  var pos_zero: fp64 := 0.0;
  var neg_zero: fp64 := -0.0;
  
  var bitwise_eq := pos_zero == neg_zero;  // ERROR: ±0 check fails
}

// PART 4: Soundness Tests

// Variable declarations are checked
method TestVariableDeclarationSoundness() {
  var s1: set<fp64> := {1.0, 2.0};
  var s2: set<fp64> := {1.0, 2.0};
  var eq := s1 == s2;  // ERROR: checked in declaration
  print eq;
}

// Assignments are checked too
method TestExplicitAssignmentWorks() {
  var s1: set<fp64> := {1.0, 2.0};
  var s2: set<fp64> := {1.0, 2.0};
  var eq: bool;
  eq := s1 == s2;  // ERROR: checked in assignment
}
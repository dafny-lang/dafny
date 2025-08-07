// RUN: %testDafnyForEachResolver --expect-exit-code=2 "%s"

// Comprehensive test that fp64 type mismatch errors are properly caught by the resolver

method BasicArithmeticErrors() {
  var fp_val: fp64 := ~3.14;
  var real_val: real := 2.5;
  var int_val: int := 42;

  // Addition errors
  var add1 := fp_val + real_val;  // Error: fp64 arithmetic requires both operands to be fp64
  var add2 := fp_val + int_val;   // Error: fp64 arithmetic requires both operands to be fp64
  var add3 := real_val + fp_val;  // Error: fp64 arithmetic requires both operands to be fp64
  var add4 := int_val + fp_val;   // Error: fp64 arithmetic requires both operands to be fp64
  
  // Subtraction errors
  var sub1 := fp_val - real_val;  // Error: fp64 arithmetic requires both operands to be fp64
  var sub2 := fp_val - int_val;   // Error: fp64 arithmetic requires both operands to be fp64
  var sub3 := real_val - fp_val;  // Error: fp64 arithmetic requires both operands to be fp64
  var sub4 := int_val - fp_val;   // Error: fp64 arithmetic requires both operands to be fp64
  
  // Multiplication errors
  var mul1 := fp_val * real_val;  // Error: fp64 arithmetic requires both operands to be fp64
  var mul2 := fp_val * int_val;   // Error: fp64 arithmetic requires both operands to be fp64
  var mul3 := real_val * fp_val;  // Error: fp64 arithmetic requires both operands to be fp64
  var mul4 := int_val * fp_val;   // Error: fp64 arithmetic requires both operands to be fp64
  
  // Division errors
  var div1 := fp_val / real_val;  // Error: fp64 arithmetic requires both operands to be fp64
  var div2 := fp_val / int_val;   // Error: fp64 arithmetic requires both operands to be fp64
  var div3 := real_val / fp_val;  // Error: fp64 arithmetic requires both operands to be fp64
  var div4 := int_val / fp_val;   // Error: fp64 arithmetic requires both operands to be fp64
}

method AssignmentErrors() {
  var fp_var: fp64;
  var real_var: real := 2.5;
  var int_var: int := 42;
  
  fp_var := real_var;  // Error: mismatched types (expected fp64, got real)
  fp_var := int_var;   // Error: mismatched types (expected fp64, got int)
  
  real_var := fp_var;  // Error: mismatched types (expected real, got fp64)
  int_var := fp_var;   // Error: mismatched types (expected int, got fp64)
}

method ComparisonErrors() {
  var fp_val: fp64 := ~3.14;
  var real_val: real := 2.5;
  var int_val: int := 42;
  
  // Comparisons between fp64 and other numeric types should fail
  var cmp1 := fp_val == real_val;  // Error: arguments must have comparable types
  var cmp2 := fp_val == int_val;   // Error: arguments must have comparable types
  var cmp3 := fp_val != real_val;  // Error: arguments must have comparable types
  var cmp4 := fp_val != int_val;   // Error: arguments must have comparable types
  var cmp5 := fp_val < real_val;   // Error: arguments must have the same type
  var cmp6 := fp_val <= int_val;   // Error: arguments must have the same type
  var cmp7 := real_val > fp_val;   // Error: arguments must have the same type
  var cmp8 := int_val >= fp_val;   // Error: arguments must have the same type
}

function FunctionWithFp64(x: fp64): fp64 {
  x + ~1.0
}

function FunctionWithReal(x: real): real {
  x + 1.0
}

function FunctionWithInt(x: int): int {
  x + 1
}

method FunctionCallErrors() {
  var fp_val: fp64 := ~3.14;
  var real_val: real := 2.5;
  var int_val: int := 42;
  
  // Wrong argument types
  var f1 := FunctionWithFp64(real_val);  // Error: incorrect argument type (expected fp64, got real)
  var f2 := FunctionWithFp64(int_val);   // Error: incorrect argument type (expected fp64, got int)
  var f3 := FunctionWithReal(fp_val);    // Error: incorrect argument type (expected real, got fp64)
  var f4 := FunctionWithInt(fp_val);     // Error: incorrect argument type (expected int, got fp64)
  
  // Wrong return type usage
  var fp_result: fp64 := FunctionWithReal(real_val);   // Error: mismatched types
  var real_result: real := FunctionWithFp64(fp_val);   // Error: mismatched types
}

method MethodWithFp64Param(x: fp64) {
  print x;
}

method MethodWithRealParam(x: real) {
  print x;
}

method MethodCallErrors() {
  var fp_val: fp64 := ~3.14;
  var real_val: real := 2.5;
  var int_val: int := 42;
  
  MethodWithFp64Param(real_val);  // Error: incorrect argument type
  MethodWithFp64Param(int_val);   // Error: incorrect argument type
  MethodWithRealParam(fp_val);    // Error: incorrect argument type
}

method ArrayErrors() {
  var fp_array: array<fp64> := new fp64[10];
  var real_array: array<real> := new real[10];
  var int_array: array<int> := new int[10];
  
  fp_array[0] := 2.5;       // Error: mismatched types (real literal needs ~ for fp64)
  fp_array[1] := 42;        // Error: mismatched types (expected fp64, got int)
  real_array[0] := ~2.5;    // Error: mismatched types (expected real, got fp64)
  
  var fp_val: fp64 := real_array[0];   // Error: mismatched types
  var real_val: real := fp_array[0];   // Error: mismatched types
}

method SequenceErrors() {
  var fp_seq: seq<fp64> := [~1.0, ~2.0];
  var real_seq: seq<real> := [1.0, 2.0];
  var int_seq: seq<int> := [1, 2];
  
  var mixed_seq1 := fp_seq + real_seq;   // Error: type mismatch
  var mixed_seq2 := fp_seq + int_seq;    // Error: type mismatch
  
  var elem1: fp64 := real_seq[0];        // Error: mismatched types
  var elem2: real := fp_seq[0];          // Error: mismatched types
}

method SetErrors() {
  var fp_set: set<fp64> := {~1.0, ~2.0};
  var real_set: set<real> := {1.0, 2.0};
  
  var mixed_set1 := fp_set + real_set;   // Error: type mismatch
  var mixed_set2 := fp_set * real_set;   // Error: type mismatch
  var mixed_set3 := fp_set - real_set;   // Error: type mismatch
  
  var contains1 := ~1.0 in real_set;     // Error: type mismatch
  var contains2 := 1.0 in fp_set;        // Error: type mismatch (needs ~)
}

method MapErrors() {
  var fp_map: map<fp64, int> := map[~1.0 := 1];
  var real_map: map<real, int> := map[1.0 := 1];
  
  var lookup1 := 1.0 in fp_map;          // Error: type mismatch (needs ~)
  var lookup2 := ~1.0 in real_map;       // Error: type mismatch
  
  var value1 := fp_map[1.0];             // Error: type mismatch (needs ~)
  var value2 := real_map[~1.0];          // Error: type mismatch
}

datatype MixedType = MakeFp64(fp64) | MakeReal(real) | MakeInt(int)

method DatatypeErrors() {
  var fp_val: fp64 := ~3.14;
  var real_val: real := 2.5;
  
  // These should be OK - just to show datatypes can contain fp64
  var d1 := MakeFp64(fp_val);
  var d2 := MakeReal(real_val);
  
  // But these should fail
  var d3 := MakeFp64(real_val);         // Error: incorrect argument type
  var d4 := MakeReal(fp_val);           // Error: incorrect argument type
}

method TypeParameterErrors<T>(x: T) {
  var fp_val: fp64 := ~3.14;
  var result: T := fp_val;              // Error: mismatched types (fp64 is not T)
}

method ConditionalErrors() {
  var fp_val: fp64 := ~3.14;
  var real_val: real := 2.5;
  var int_val: int := 42;
  
  var cond1 := if true then fp_val else real_val;   // Error: mismatched types in branches
  var cond2 := if true then fp_val else int_val;    // Error: mismatched types in branches
  var cond3 := if true then real_val else fp_val;   // Error: mismatched types in branches
}

// Note: Literal errors (3.14 and 0.1 without ~) are tested separately in Fp64InexactLiteralErrors.dfy
// because they are caught in an early phase before other type errors.
method LiteralUsageErrors() {
  var fp1: fp64 := ~3.14;      // OK with ~
  var real1: real := ~3.14;    // Error: ~ prefix can only be used on fp64 literals
}

method ModuloError() {
  var fp_val: fp64 := ~3.14;
  var int_val: int := 42;
  
  var mod1 := fp_val % ~2.0;   // Error: % not supported for fp64
  var mod2 := fp_val % int_val; // Error: % not supported for fp64
}
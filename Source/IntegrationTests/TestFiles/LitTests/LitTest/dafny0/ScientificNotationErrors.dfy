// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test error cases for scientific notation and trailing dot literals

method MalformedScientificNotation() {
  // Incomplete scientific notation - missing exponent
  var a := 1.23e;      // Error: incomplete
  var b := 5.e;        // Error: incomplete  
  
  // Missing digits after decimal in scientific notation
  var c := 1.e;        // Error: no digits after dot and e
}

method InvalidUnderscorePlacement() {
  // Invalid underscore before dot
  var a := 1_.;        // Error: underscore before dot
  var b := 1_2_.;      // Error: underscore before dot
  
  // Invalid underscore in exponent
  var c := 1.e_2;      // Error: underscore at start of exponent
  var d := 1.e2_;      // Error: underscore at end of exponent
}

method InvalidCombinations() {
  // Multiple e's
  var a := 1.23e2e3;   // Error: multiple exponents
  
  // Invalid characters in scientific notation
  var b := 1.23f5;     // Error: 'f' instead of 'e'
  var c := 1.23E+;     // Error: missing exponent after +
  var d := 1.23E-;     // Error: missing exponent after -
}

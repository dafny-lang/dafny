// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test error cases for scientific notation, trailing-dot shorthand, and leading-dot shorthand

method MalformedScientificNotation() {
  // Incomplete scientific notation - missing exponent
  var a := 1.23e;      // Error: incomplete
  var b := 5e;         // Error: incomplete (no trailing-dot shorthand syntax)

  // Invalid exponent syntax
  var c := 1.23e+;     // Error: missing digits after +
  var d := 1.23e-;     // Error: missing digits after -
}

method InvalidUnderscorePlacement() {
  // Invalid underscore before dot
  var a := 1_.;        // Error: underscore before dot
  var b := 1_2_.;      // Error: underscore before dot

  // Invalid underscore in exponent
  var c := 1.23e_2;    // Error: underscore at start of exponent
  var d := 1.23e2_;    // Error: underscore at end of exponent
}

method InvalidCombinations() {
  // Multiple e's
  var a := 1.23e2e3;   // Error: multiple exponents

  // Invalid characters in scientific notation
  var b := 1.23f5;     // Error: 'f' instead of 'e'
  var c := 1.23E2;     // Error: uppercase 'E' not supported
}

method InvalidLeadingDotShorthand() {
  // Leading-dot shorthand with space (should be error due to tokenization)
  var a := . 5;        // Error: space between dot and digits
  var b := . 5e2;      // Error: space between dot and digits

  // Invalid leading-dot shorthand combinations
  var c := ..5;        // Error: double dot
  var d := .e2;        // Error: no digits after dot before e
}

method InvalidWhitespaceAroundDots() {
  // Whitespace before trailing dot (should be error)
  var a := 1 .;        // Error: space before trailing dot
  var b := 123 .;      // Error: space before trailing dot

  // Whitespace after leading dot (should be error) 
  var c := . 5;        // Error: space after leading dot
  var d := . 25;       // Error: space after leading dot

  // Whitespace around normal decimal dot (should be error)
  var e := 1 . 5;      // Error: spaces around decimal dot
}

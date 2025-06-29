// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test error cases for leading dot literals

method TestLeadingDotErrors() {
  // This should be valid
  var valid := .5;
  
  // These should cause parse errors:
  var invalid1 := .;        // Just a dot - should be invalid
  var invalid2 := .e5;      // No digits after dot before exponent
}

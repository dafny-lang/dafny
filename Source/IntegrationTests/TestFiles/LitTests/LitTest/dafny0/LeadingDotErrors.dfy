// RUN: %exits-with 2 %resolve "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Test error cases for leading dot literals

method TestLeadingDotErrors() {
  // These should be valid (restricted leading dot support)
  var valid1 := .50;    // 2+ digits
  var valid2 := .5e2;   // single digit with exponent
  
  // These should cause parse errors:
  var invalid1 := .;        // Just a dot - should be invalid
  var invalid2 := .e5;      // No digits after dot before exponent
  
  // Note: .5 (single digit without exponent) is not supported to avoid conflicts with tuple access
}

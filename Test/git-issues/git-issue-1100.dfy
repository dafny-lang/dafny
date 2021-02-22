// RUN: %dafny  /compile:3 /compileTarget:cpp ../c++/arrays.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

// Test compilation of a file in another directory

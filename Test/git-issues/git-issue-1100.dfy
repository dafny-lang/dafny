// RUN: %dafny  /compile:3 /compileTarget:cpp %S/../c++/arrays.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

// Test compilation of a file in another directory

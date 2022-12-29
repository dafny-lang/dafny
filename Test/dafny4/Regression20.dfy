// RUN: %exits-with 2 %baredafny verify %args "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// The type name "bv" once crashed the resolver

method M(x: bv)  // error: undeclared type bv

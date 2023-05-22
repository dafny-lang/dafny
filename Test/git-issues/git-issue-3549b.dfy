// RUN: %exits-with 1 %baredafny resolve "" 2> "%t"
// RUN: %diff "%s.expect" "%t"

// RUN: %exits-with 1 %baredafny resolve "" > "%t"
// RUN: %diff "%s.expect" "%t"

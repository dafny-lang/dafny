// RUN: %exits-with 1 %baredafny resolve "" > "%t" 2>&1
// RUN: %diff "%s.expect" "%t"

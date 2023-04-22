// RUN: %exits-with 1 %baredafny "" > "%t" 2>&1
// RUN: %diff "%s.expect" "%t"

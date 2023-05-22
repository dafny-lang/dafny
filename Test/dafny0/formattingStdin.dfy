// RUN: %exits-with 1 %baredafny format --stdin 2> "%t"
// RUN: %diff "%s.expect" "%t"

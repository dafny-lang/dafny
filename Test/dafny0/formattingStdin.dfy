// RUN: %exits-with 2 %baredafny format --stdin 2> "%t"
// RUN: %diff "%s.expect" "%t"

// RUN: %exits-with 1 %baredafny verify --solver-plugin x test.dfy &> "%t"
// RUN: %diff "%s.expect" "%t"

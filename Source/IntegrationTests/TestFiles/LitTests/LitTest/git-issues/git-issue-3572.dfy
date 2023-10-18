// RUN: %exits-with 1 %baredafny verify --solver-plugin x test.dfy 2> "%t"
// RUN: %diff "%s.expect" "%t"

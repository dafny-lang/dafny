// RUN: ! %baredafny verify %args --function-syntax:2 null.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

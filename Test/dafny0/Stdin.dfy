// RUN: %exits-with 0 %stdin "module A{}" %baredafny verify --stdin > "%t"
// RUN: %diff "%s.expect" "%t"


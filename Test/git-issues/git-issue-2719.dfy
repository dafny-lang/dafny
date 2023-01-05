// RUN: %baredafny verify %args_0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method Test() {}
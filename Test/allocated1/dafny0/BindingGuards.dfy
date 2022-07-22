// RUN: %dafny_0 /verifyAllModules /allocated:1 /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/BindingGuards.dfy"

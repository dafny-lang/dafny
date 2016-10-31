// RUN: %dafny /verifyAllModules /allocated:1 /print:"%t.print" /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/DiscoverBounds.dfy"

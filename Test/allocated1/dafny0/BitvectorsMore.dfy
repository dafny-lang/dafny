// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /print:"%t.print" /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/BitvectorsMore.dfy"

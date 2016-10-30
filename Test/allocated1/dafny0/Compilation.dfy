// RUN: %dafny /verifyAllModules /allocated:1 /compile:3 /autoTriggers:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Compilation.dfy"

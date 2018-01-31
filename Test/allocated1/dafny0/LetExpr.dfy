// RUN: %dafny /verifyAllModules /allocated:1 /compile:0 /print:"%t.print" /dprint:"%t.dprint.dfy" "%s" > "%t"
// RUN: %dafny /verifyAllModules /allocated:1 /noVerify /compile:0 "%t.dprint.dfy" >> "%t"
include "../../dafny0/LetExpr.dfy"

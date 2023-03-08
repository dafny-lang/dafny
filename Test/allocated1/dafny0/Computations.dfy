// RUN: %dafny /verifyAllModules /allocated:1 /proverOpt:O:smt.qi.eager_threshold=25 /compile:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Computations.dfy"

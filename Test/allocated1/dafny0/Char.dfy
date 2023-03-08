// RUN: %exits-with 4 %dafny /verifyAllModules /allocated:1 /compile:0 /unicodeChar:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Char.dfy"

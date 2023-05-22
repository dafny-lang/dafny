// RUN: %dafny /verifyAllModules /allocated:1 /compile:3 /unicodeChar:0 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/Strings.dfy"

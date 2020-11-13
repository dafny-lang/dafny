// RUN: %dafny /verifyAllModules /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../docs/_includes/Example-BV2.dfy"

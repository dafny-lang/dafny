// RUN: %dafny /verifyAllModules /allocated:1 /dprint:- /env:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
include "../../dafny0/BindingGuardsResolution.dfy"

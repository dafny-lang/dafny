// RUN: %dafny /compile:0 /deprecation:0 /verifySnapshots:2 /traceCaching:1 %S/Inputs/Snapshots5.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

// RUN: %dafny_0 /compile:0 /verifySnapshots:2 /traceCaching:1 %S/Inputs/Snapshots0.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

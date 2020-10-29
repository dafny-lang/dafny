// RUN: %dafny /compile:0 /verifySnapshots:2 /traceCaching:1 Inputs/Snapshots6.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

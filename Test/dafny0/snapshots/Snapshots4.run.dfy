// RUN: %dafny /compile:0 /verifySnapshots:2 /traceCaching:1 Inputs/Snapshots4.dfy > "%t"
// RUN: %diff "%s.expect" "%t"

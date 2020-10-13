// RUN: %dafny /compile:0 /verifySnapshots:3 /traceCaching:1 Inputs/Snapshots9.dfy > "%t"
// RUN: %diff "%s.expect" "%t"
